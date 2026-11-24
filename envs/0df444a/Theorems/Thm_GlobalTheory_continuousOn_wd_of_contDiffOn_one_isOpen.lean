-- Prove2me | Theorems.Thm_GlobalTheory_continuousOn_wd_of_contDiffOn_one_isOpen
-- name    : GlobalTheory.continuousOn_wd_of_contDiffOn_one_isOpen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:27.265613+00:00
-- url     : https://prove2.me/theorems/6bdb8581-4876-4f07-a794-e81f7db26490
-- title:
--   Global Theory: continuous On wd of cont Diff On one is Open
-- statement:
--   The Global Theory construction uses the continuous On wd of cont Diff On one is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwo.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwo.lean#L26-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.continuousOn_wd_of_contDiffOn_one_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (j : Fin n) :
    ContinuousOn (wd n j g) U := by sorry
