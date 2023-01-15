import copy
import glob
import os
import pickle
import py_miz_controller

MML_VCT_PATH = "/home/g063ff/emwiki/emwiki/mmlfiles/mml.vct"
MML_ABSTR_DIR = "/home/g063ff/emwiki/emwiki/mmlfiles/abstr/"

# TODO 型を削減する方法を選択:
# 1: 何もしない(型を削減しない)
# 2: of以降を削除
# 3: of以降を削除し, 最後のトークンを残す.
REDUCTION_TYPE_ALGORITHM = 1

miz_controller = py_miz_controller.MizController()


def save_byte_index_of_lines(input, output):
    """
    inputを行ごとにバイト数を求め、outputに保存する関数
    """
    with open(input, "rb") as f:
        byte_indices = []
        byte_indices.append(0)
        with open(output, "wb") as fi:
            while True:
                a = f.readline()
                if not a:
                    break
                byte_indices.append(f.tell())

            pickle.dump(byte_indices, fi)


def get_theorem_and_definition_tokens_list(token_table, file_name):
    """
    入力: absファイルのtoken_table
    出力: 定理, 定義ごとに分割されたtokensのリスト
    例:[[定理1のtoken, 定理1のtoken, 定理1のtoken], [定理2のtoken, 定理2のtoken, 定理2のtoken], ...]
    """
    upper_article_name = file_name.upper().split('.')[0]
    state = {
        "is_theorem": False,  # theoremの中にあるかどうか　theorem ~~ ; までの部分
        "is_definition_block": False,  # definitionのブロック内にあるかどうか  definition ~~ end; までの部分
        "is_definition": False  # definitionのラベル内かどうか
    }
    token_num = token_table.token_num
    tokens_list = []
    current_statement = []
    common_definition_statement = []
    for i in range(token_num):
        token = token_table.token(i)
        token_text = token.text
        token_type = token.token_type
        if(state["is_theorem"]):
            current_statement.append(token)
            # 定理は";"で終了する
            if(token_text == ";"):
                state["is_theorem"] = False
                tokens_list.append(current_statement)
                current_statement = []
        # 一つのdefinitionブロック内に複数の定義が記述される場合がある．
        if(state["is_definition_block"]):
            if(token_text == "end"):
                state["is_definition_block"] = False
                common_definition_statement = []
            elif(token_text == ";"):
                current_statement.append(token)
                # 定義は共通部分とラベルがついた部分から成る
                if(state["is_definition"]):
                    state["is_definition"] = False
                    tokens_list.append(common_definition_statement + current_statement)
                    current_statement = []
                # ラベル内でない場合, 共通部分として保存
                else:
                    common_definition_statement.extend(current_statement)
                    current_statement = []
            # コメントの始まりがarticle名と一致するかどうかで, ラベル名か判断.
            # :: ABCMIZ_0:def 1 -> ABCMIZ_0:def1
            elif(token_type == py_miz_controller.TokenType.COMMENT and token_text.replace('::', '').replace(' ', '').startswith(upper_article_name + ":def")):
                current_statement.append(token)
                state["is_definition"] = True
            else:
                current_statement.append(token)
        elif(token_text == "theorem"):
            state["is_theorem"] = True
        elif(token_text == "definition"):
            state["is_definition_block"] = True

    return tokens_list


def get_abs_dictionary_line(theorem_and_definition_tokens, file_name):
    """
    入力: 定義または定理のtokenのリスト
    出力: abs_dictionary.txtのフォーマット(definition/theorem 行数 ファイル名 ラベル 定理本文)
    例: definition 51 abcmiz_0.abs ABCMIZ_0:def1 let T be RelStr ; attr T is Noetherian means the InternalRel of T is co-well_founded ;
    """
    upper_article_name = file_name.upper().split('.')[0]
    title = ""
    line_no = ""
    label = ""
    text = ""
    for token in theorem_and_definition_tokens:
        token_text = token.text
        token_type = token.token_type
        if(token_type == py_miz_controller.TokenType.COMMENT):
            split_token_text = token_text.split()
            # ラベルを表すコメントの場合
            if(len(split_token_text) > 1 and split_token_text[1].startswith(upper_article_name)):
                if("def" in split_token_text[1]):
                    title = "definition"
                    label = split_token_text[1] + split_token_text[2]
                else:
                    title = "theorem"
                    label = split_token_text[1]
                line_no = str(token.line_number)
            else:
                pass
        else:
            text += token_text + " "
    return f"{title} {line_no} {file_name} {label} {text}"


def is_variable(token):
    return token.token_type == py_miz_controller.TokenType.IDENTIFIER and (token.identifier_type == py_miz_controller.IdentifierType.RESERVED or token.identifier_type == py_miz_controller.IdentifierType.VARIABLE)


def reduction_type(type_tokens):
    """
    型のtoken列を削減する(後の処理を共通化するために長さ1のリストを返す)
    """
    if(REDUCTION_TYPE_ALGORITHM == 1):
        return
    else:
        # of以降を削除
        for i in range(len(type_tokens)):
            if(type_tokens[i].text == "of"):
                type_tokens[i:] = []
                break
        if(REDUCTION_TYPE_ALGORITHM == 2):
            return
        elif(REDUCTION_TYPE_ALGORITHM == 3):
            if(len(type_tokens) == 0):
                return
            # 末尾が","の場合削除
            if(type_tokens[-1].text == ","):
                type_tokens.pop()
            type_token = type_tokens[-1]
            type_tokens.clear()
            type_tokens.append(type_token)


def get_common_variable_dict_list(token_table):
    """
    入力: absファイルのtoken_table
    出力: ファイル共通で使用される変数(reserveで宣言された変数)の情報
      [{variable_token: token, type_tokens: [token, token, ...]}, {}, {}]
    例:
    reserve i for Nat,
      j for Element of NAT,
      X,Y,x,y,z for set;
    [{variable_token: i, type_tokens: [Nat]},
     {variable_token: j, type_tokens: [Element, of, NAT]},
     {variable_token: X, type_tokens: [set]},
     {variable_token: Y, type_tokens: [set]},
     ...]
    """
    state = {
        "is_reserve_block": False,  # reserveのblock内にあるかどうか  reserve ~ ;までの部分
        "the_for_has_appeared": False  # reserveのblock内でforが出現したかどうか
    }
    token_num = token_table.token_num
    variable_dict_list = []
    current_variable_dict_list = []
    current_type_tokens = []

    # ひとつの変数宣言が終了する際に呼ばれる
    def resolve_reserve_block():
        reduction_type(current_type_tokens)
        for dict in current_variable_dict_list:
            dict["type_tokens"] = copy.copy(current_type_tokens)
        variable_dict_list.extend(current_variable_dict_list)
        current_variable_dict_list.clear()
        current_type_tokens.clear()

    for i in range(token_num):
        token = token_table.token(i)
        token_line_number = token.line_number
        token_text = token.text
        if(state["is_reserve_block"]):
            if(state["the_for_has_appeared"]):
                # reserve blockは";"で終了
                if(token_text == ";"):
                    resolve_reserve_block()
                    state["is_reserve_block"] = False
                    state["the_for_has_appeared"] = False
                    continue
                """
                forが出現し, ;が出現する前に再びforが出現する場合の処理
                例1:
                reserve q for pure expression of C, a_Type C,
                  A for finite Subset of QuasiAdjs C;
                例2:
                reserve X for ARS, a,b,c,u,v,w,x,y,z for Element of X;
                """
                if(token_text == "for"):
                    new_variable_tokens = []
                    # 変数と","以外のtokenが出現するまでを, ひとつの変数宣言部分とする. それ以降に出現した変数は新しい変数宣言部分として処理を再開する
                    while(len(current_type_tokens)):
                        # 改行があった場合, そこを境界とする
                        if(current_type_tokens[-1].line_number < token_line_number):
                            resolve_reserve_block()
                            for new_variable_token in new_variable_tokens:
                                current_variable_dict_list.append({"variable_token": new_variable_token})
                            break
                        else:
                            poped_token = current_type_tokens.pop()
                            if(poped_token.text == ","):
                                pass
                            elif(is_variable(poped_token)):
                                new_variable_tokens.append(poped_token)
                            else:
                                current_type_tokens.append(poped_token)
                                resolve_reserve_block()
                                for new_variable_token in new_variable_tokens:
                                    current_variable_dict_list.append({"variable_token": new_variable_token})
                else:
                    current_type_tokens.append(token)
            # reserve block内でforが出現する前の処理. 出現した変数を記録する(複数宣言される場合もある)
            else:
                if(token_text == "for"):
                    state["the_for_has_appeared"] = True
                elif(is_variable(token)):
                    current_variable_dict_list.append({"variable_token": token})
        elif(token_text == "reserve"):
            state["is_reserve_block"] = True
    return variable_dict_list


def get_number_of_variable(tokens):
    """
    入力: 定義または定理のtokenのリスト
    出力: 変数の種類数
    """
    variable_token_list = []
    for token in tokens:
        if(is_variable(token)):
            if(token.ref_token is None):
                variable_token_list.append(token)
            else:
                filtered_list = list(filter(lambda variable_token: token.ref_token == variable_token, variable_token_list))
                if(len(filtered_list) == 0):
                    variable_token_list.append(token)
    return len(variable_token_list)


def get_variable_declaration_statement_text(variable_declaration_statement_token_list, variable_dict_list):
    # 変数宣言部分のテキストを変数を型に置き換える処理
    processed_text = ""
    for variable_declaration_statement_token in variable_declaration_statement_token_list:
        filtered_list = list(filter(lambda variable_dict: variable_dict["variable_token"] == variable_declaration_statement_token, variable_dict_list))
        if(len(filtered_list) > 0):
            variable_dict = filtered_list[0]
            # variable_dict["type_tokens"]には型のtokenリストが格納されている
            for type_token in variable_dict["type_tokens"]:
                processed_text += type_token.text + " "
        else:
            processed_text += variable_declaration_statement_token.text + " "
    return processed_text


def replace_variable_with_type(tokens, common_variable_dict_list):
    """
    入力: 定義または定理のtokenのリスト, ファイル共通の変数情報のリスト
    出力: モデルへ入力するための処理を行った定理本文(変数を型名に置き換え, ","と";"を削除, 変数の種類の数だけ末尾に"____"を追加)
    処理前: let T be RelStr ; attr T is Noetherian means the InternalRel of T is co-well_founded ;
    処理後: let RelStr be RelStr  attr RelStr is Noetherian means the InternalRel of RelStr is co-well_founded
    """
    state = {
        "is_variable_declaration_statement": False,  # 変数宣言部分内にあるかどうか(for|let|given|ex ~~ st|holds|;|suchまでの部分)
        "the_being_has_appeared": False  # 変数宣言部分内でbeing|beが出現したかどうか
    }
    number_of_variable = get_number_of_variable(tokens)
    variable_dict_list = copy.copy(common_variable_dict_list)  # variable_dict_listは定理ごとにcommon_variable_dict_listを上書きする
    variable_declaration_statement_token_list = []  # 変数宣言されている部分のtoken列を一時的に保存するリスト
    current_variable_list = []  # 宣言された変数を一時的に保存するリスト
    current_type_tokens = []  # 宣言された変数の型のtoken列を保存するリスト
    keywords_of_start_of_variable_declaration_statement = ["for", "let", "given", "ex"]  # 変数宣言の部分が開始されるキーワード
    keywords_of_end_of_variable_declaration_statement = ["st", "holds", ";", "such"]  # 変数宣言の部分が終了するキーワード
    processed_text = ""

    # 変数宣言部分が終了するときに呼ばれる. 変数と型の対応の保存, 変数宣言部分のテキストの生成, 一時リストの初期化を行う.
    def resolve_variable_declaration_statement_text():
        nonlocal processed_text
        current_variable_dict_list = []
        # 型の情報がないまま変数宣言部分が終了した場合. 例: let c;
        if(len(current_type_tokens) == 0):
            for variable_token in current_variable_list:
                ref_token = variable_token.ref_token
                if(ref_token is None):
                    continue
                # variable_tokenがref_tokenを持っており, variable_dict_listに存在する場合, その情報を元に新しく変数を登録
                filtered_list = list(filter(lambda variable_dict: variable_dict["variable_token"] == ref_token, variable_dict_list))
                if(len(filtered_list) > 0):
                    variable_dict_list.append({"variable_token": variable_token, "type_tokens": copy.copy(filtered_list[0]["type_tokens"])})
        else:
            reduction_type(current_type_tokens)
            for variable_token in current_variable_list:
                current_variable_dict_list.append({"variable_token": variable_token, "type_tokens": copy.copy(current_type_tokens)})
            variable_dict_list.extend(current_variable_dict_list)
        processed_text += get_variable_declaration_statement_text(variable_declaration_statement_token_list, variable_dict_list)
        variable_declaration_statement_token_list.clear()
        current_variable_list.clear()
        current_type_tokens.clear()

    for token_number, token in enumerate(tokens):
        token_text = token.text
        token_type = token.token_type
        ref_token = token.ref_token
        # コメントは無視
        if(token_type == py_miz_controller.TokenType.COMMENT):
            continue
        # 変数宣言部分の処理
        elif(state["is_variable_declaration_statement"]):
            variable_declaration_statement_token_list.append(token)
            # 変数宣言部分で, be/beingが出現した後の処理
            if(state["the_being_has_appeared"]):
                # 変数宣言部分の終了
                if(token_text in keywords_of_end_of_variable_declaration_statement):
                    resolve_variable_declaration_statement_text()
                    state["is_variable_declaration_statement"] = False
                    state["the_being_has_appeared"] = False
                # 新しい変数が続けて宣言される場合(for, let等のキーワードが出現する場合)
                # 例: for T being Noetherian sup-Semilattice for I being Ideal of T holds ...
                elif(token_text in keywords_of_start_of_variable_declaration_statement):
                    resolve_variable_declaration_statement_text()
                    state["the_being_has_appeared"] = False
                # 新しい変数が続けて宣言される場合(for, let等のキーワードが出現しない場合)
                # 例: for l being quasi-loci, x being variable holds ...
                elif(token_text == "be" or token_text == "being"):
                    current_type_tokens.pop()
                    # beingのひとつ前のtoken(新しい変数)を取り出す. 例だとfor l being quasi-loci, x being までがリストにあるので2回popする
                    variable_declaration_statement_token_list.pop()
                    new_variable_token = variable_declaration_statement_token_list.pop()
                    resolve_variable_declaration_statement_text()
                    current_variable_list.append(new_variable_token)
                    variable_declaration_statement_token_list.extend([new_variable_token, token])
                # 変数宣言部分で, be/beingが出現した後, 上記の条件に該当しない場合は型のtoken列の末尾に追加
                else:
                    current_type_tokens.append(token)
            elif(token_text == "be" or token_text == "being"):
                state["the_being_has_appeared"] = True
            # 変数宣言部分で, be/beingが出現しておらず, 変数が出現した際の処理
            elif(is_variable(token)):
                current_variable_list.append(token)
            # 変数宣言部分で, be/beingがまだ出現しておらず, 終了のキーワードが出現したときの処理
            # 例: let c;
            elif(token_text in keywords_of_end_of_variable_declaration_statement):
                resolve_variable_declaration_statement_text()
                state["is_variable_declaration_statement"] = False
        # 変数宣言部分でなく, let, for等のキーワードが出現したときの処理
        elif(token_text in keywords_of_start_of_variable_declaration_statement):
            state["is_variable_declaration_statement"] = True
            variable_declaration_statement_token_list.append(token)
        # 変数宣言部分でなく, tokenがref_tokenをもっている場合, 変数の型情報がないか調査し, あれば置き換える
        elif(ref_token):
            have_type_info = False
            for variable_dict in variable_dict_list:
                if(ref_token.id == variable_dict["variable_token"].id):
                    # variable_dict["type_tokens"]には型のtokenリストが格納されている
                    for type_token in variable_dict["type_tokens"]:
                        processed_text += type_token.text + " "
                    have_type_info = True
                    break
            # 型の情報がない変数の処理
            if not(have_type_info):
                processed_text += "___" + " "
        else:
            processed_text += token_text + " "

    # "," ";" は、ほぼすべての定理に存在しておりノイズになる可能性が高いため除く.
    return f"{processed_text.replace(',', '').replace(';', '')} {'____ '*number_of_variable}"


def replace_variable_with_underscore(tokens, common_variable_dict_list):
    """
    入力: 定義または定理のtokenのリスト, ファイル共通の変数情報のリスト
    出力: 変数を___で置き換えた定理本文
    処理前: let T be RelStr ; attr T is Noetherian means the InternalRel of T is co-well_founded ;
    処理後: let ___ be RelStr  attr ___ is Noetherian means the InternalRel of ___ is co-well_founded
    """
    processed_text = ""
    number_of_variable = get_number_of_variable(tokens)
    for token in tokens:
        # コメントは無視
        if(token.token_type == py_miz_controller.TokenType.COMMENT):
            continue
        elif(is_variable(token)):
            processed_text += "___" + " "
        else:
            processed_text += token.text + " "

    # "," ";" は、ほぼすべての定理に存在しておりノイズになる可能性が高いため除く.
    return f"{processed_text.replace(',', '').replace(';', '')} {'____ '*number_of_variable}"


def create_abs_dictionary_and_document_vectors():
    """
    absファイルからabs_dictionary.txtとdocument_vectors.txt(変数に型情報をつけたもの)を作成する関数

    abs_dictionary.txt:
        (definition or theorem)  (行数)  (ファイル名)  (ラベル名)       (テキスト)
        definition               51      abcmiz_0.abs  BCMIZ_0:def 1   let T be RelStr;   attr T is Noetherian means   the InternalRel of T is co-well_founded;

    document_vectors.txt:
        let ___ be RelStr ; attr ___ is Noetherian means the InternalRel of ___ is co-well_founded ; ____
    """
    cwd = os.getcwd()
    try:
        path = MML_ABSTR_DIR
        os.chdir(path)
        abs_files = sorted(glob.glob("*.abs"))
    finally:
        os.chdir(cwd)

    # TODO document_vectorsを生成する際に使用する関数を選択する(変数を__とするか, 型で置き換えるか)
    get_document_vectors_line = replace_variable_with_type
    # get_document_vectors_line = replace_variable_with_underscore
    with open("abs_dictionary.txt", "w") as file_abs_dictionary, open("document_vectors.txt", "w") as file_document_vectors:
        for file_name in abs_files:
            # file_name = "abcmiz_1.abs"
            miz_controller.exec_file(MML_ABSTR_DIR + file_name, MML_VCT_PATH)
            token_table = miz_controller.token_table
            # ファイルの定義定理を, token列ごとに分割したリストを取得
            theorem_and_definition_tokens_list = get_theorem_and_definition_tokens_list(token_table, file_name)
            # ファイル共通の変数の型情報(reserveで宣言された変数)を取得
            common_variable_dict_list = get_common_variable_dict_list(token_table)
            # abs_dictionaryとdocument_vectorsに書き込み(1列がひとつの定義定理に対応している)
            for theorem_and_definition_tokens in theorem_and_definition_tokens_list:
                file_abs_dictionary.write(
                    f"{get_abs_dictionary_line(theorem_and_definition_tokens, file_name)} \n")
                file_document_vectors.write(
                    f"{get_document_vectors_line(theorem_and_definition_tokens, common_variable_dict_list)} \n")


def parse_on_search(query, algorithm=1):
    miz_controller.exec_buffer(query, MML_VCT_PATH)
    token_table = miz_controller.token_table
    common_variable_dict_list = get_common_variable_dict_list(token_table)
    token_list = []
    # replace_variable_with_typeはtokenのリストを入力として受け取るためtoken_tableのtokenをリストに格納
    for i in range(token_table.token_num):
        token = token_table.token(i)
        token_list.append(token)
    if algorithm == 1:
        processed_text = replace_variable_with_underscore(token_list, common_variable_dict_list)
    elif algorithm == 2:
        processed_text = replace_variable_with_type(token_list, common_variable_dict_list)

    return processed_text
