-- Prove2me | Theorems.Thm_NOF_eval_eq_true
-- name    : NOF.eval_eq_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:24.014734+00:00
-- url     : https://prove2.me/theorems/34e9e899-1fd9-432e-a6d4-e4abd0e92cf3
-- title:
--   NOF: eval eq true
-- statement:
--   The NOF construction uses the eval eq true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/LowerBoundEval.lean#L27-L27
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/LowerBoundEval.lean#L27-L27

module
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_ChandraFurstLipton_LowerBoundEval
set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : ZMod d → ZMod d → G} [Fintype ι]

theorem NOF.eval_eq_true {x : ι → G} : eval x = true ↔ ∑ i, x i = 0 := by sorry
