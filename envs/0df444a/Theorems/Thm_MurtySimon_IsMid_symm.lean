-- Prove2me | Theorems.Thm_MurtySimon_IsMid_symm
-- name    : MurtySimon.IsMid.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:50:34.293849+00:00
-- url     : https://prove2.me/theorems/77fd687f-5264-5f6f-a06f-0741c0797eae
-- title:
--   Is Mid: symm
-- statement:
--   The Is Mid construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L51-L53
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L51-L53

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}

theorem MurtySimon.IsMid.symm {x y u : V} (h : IsMid G x y u) : IsMid G y x u := by sorry
