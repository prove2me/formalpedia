-- Prove2me | Theorems.Thm_NOF_IsForbiddenPatternWithTip_of_forget
-- name    : NOF.IsForbiddenPatternWithTip.of_forget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:13:31.374399+00:00
-- url     : https://prove2.me/theorems/65e52520-7616-4137-b3ea-8b4506af6674
-- title:
--   Is Forbidden Pattern With Tip: of forget
-- statement:
--   The Is Forbidden Pattern With Tip construction uses the of forget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/MultidimCorners.lean#L32-L33
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/MultidimCorners.lean#L32-L33

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {a : ι → ι → G} {v : ι → G}

theorem NOF.IsForbiddenPatternWithTip.of_forget (h : ∀ i, forget i v = forget i (a i)) :
    IsForbiddenPatternWithTip a v := by sorry
