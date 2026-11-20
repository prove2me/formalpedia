-- Prove2me | Theorems.Thm_NOF_isMultidimCorner_forget_of_isForbiddenPattern
-- name    : NOF.isMultidimCorner_forget_of_isForbiddenPattern
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:13:33.881004+00:00
-- url     : https://prove2.me/theorems/a4a6227b-2dd6-49a9-8416-3fc0eb61453b
-- title:
--   NOF: is Multidim Corner forget of is Forbidden Pattern
-- statement:
--   The NOF construction uses the is Multidim Corner forget of is Forbidden Pattern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/MultidimCorners.lean#L43-L58
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/MultidimCorners.lean#L43-L58

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {a : ι → ι → G} {v : ι → G}
variable [Fintype ι] [AddCommGroup G]
variable [DecidableEq ι]

theorem NOF.isMultidimCorner_forget_of_isForbiddenPattern (a : ι → ι → G) (h : IsForbiddenPattern a)
    (hS : ∀ i, ∑ j, a i j = 0) (i : ι) :
    IsMultidimCorner (fun j ↦ forget i (a j)) (forget i (a i)) := by sorry
