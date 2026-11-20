-- Prove2me | Theorems.Thm_NOF_trivial_of_isForbiddenPattern_of_isValid_eval
-- name    : NOF.trivial_of_isForbiddenPattern_of_isValid_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:26.143848+00:00
-- url     : https://prove2.me/theorems/f5d3abff-03f7-4d53-9284-04745a9f3b52
-- title:
--   NOF: trivial of is Forbidden Pattern of is Valid eval
-- statement:
--   The NOF construction uses the trivial of is Forbidden Pattern of is Valid eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/LowerBoundEval.lean#L31-L52
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/LowerBoundEval.lean#L31-L52

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
variable [DecidableEq ι]

theorem NOF.trivial_of_isForbiddenPattern_of_isValid_eval (ha : IsForbiddenPattern a)
    (hP : P.IsValid eval t) (hE : ∀ i, eval (a i) = true) (hB : ∀ i, P.broadcast (a i) t = B) :
    ∀ i j, a i = a j := by sorry
