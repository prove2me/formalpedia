-- Prove2me | Theorems.Thm_MurtySimon_IsCrit_not_isDiag
-- name    : MurtySimon.IsCrit.not_isDiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:26.492634+00:00
-- url     : https://prove2.me/theorems/33c111de-f81f-48f4-b1b4-265c42ec1289
-- title:
--   Is Crit: not is Diag
-- statement:
--   The Is Crit construction uses the not is Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L74-L76
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L74-L76

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

theorem MurtySimon.IsCrit.not_isDiag {f : Sym2 V} (h : IsCrit G f) : ¬ f.IsDiag := by sorry
