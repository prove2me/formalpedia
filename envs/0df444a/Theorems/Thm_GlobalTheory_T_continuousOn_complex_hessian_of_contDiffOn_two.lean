-- Prove2me | Theorems.Thm_GlobalTheory_T_continuousOn_complex_hessian_of_contDiffOn_two
-- name    : GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:32:03.697518+00:00
-- url     : https://prove2.me/theorems/2ba4e224-7795-4131-8cde-35fc636af469
-- title:
--   T: continuous On complex hessian of cont Diff On two
-- statement:
--   The T construction uses the continuous On complex hessian of cont Diff On two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwoStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwoStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwo
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnComplexHessianOfContDiffOnTwoStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuousOn_complex_hessian_of_contDiffOn_two : ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l, ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by sorry
