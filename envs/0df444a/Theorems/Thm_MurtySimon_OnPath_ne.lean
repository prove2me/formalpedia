-- Prove2me | Theorems.Thm_MurtySimon_OnPath_ne
-- name    : MurtySimon.OnPath.ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:50:39.811648+00:00
-- url     : https://prove2.me/theorems/eaca112e-01e5-551e-830f-ce88ef5e31b5
-- title:
--   On Path: ne
-- statement:
--   The On Path construction uses the ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L86-L88
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L86-L88

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

theorem MurtySimon.OnPath.ne {e f : Sym2 V} (h : OnPath G e f) : e ≠ f := by sorry
