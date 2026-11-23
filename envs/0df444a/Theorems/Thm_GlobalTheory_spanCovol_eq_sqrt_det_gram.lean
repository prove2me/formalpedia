-- Prove2me | Theorems.Thm_GlobalTheory_spanCovol_eq_sqrt_det_gram
-- name    : GlobalTheory.spanCovol_eq_sqrt_det_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:55.751714+00:00
-- url     : https://prove2.me/theorems/f8c2f0cc-9aa2-4854-9b14-0a2982a935c2
-- title:
--   Global Theory: span Covol eq sqrt det gram
-- statement:
--   The Global Theory construction uses the span Covol eq sqrt det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L60-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.spanCovol_eq_sqrt_det_gram {L : Submodule ℤ E} (b : Basis ι ℤ L) :
    spanCovol L = √(gram ℝ fun i => (b i : E)).det := by sorry
