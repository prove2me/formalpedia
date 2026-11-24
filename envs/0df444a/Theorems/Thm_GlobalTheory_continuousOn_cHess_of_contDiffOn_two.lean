-- Prove2me | Theorems.Thm_GlobalTheory_continuousOn_cHess_of_contDiffOn_two
-- name    : GlobalTheory.continuousOn_cHess_of_contDiffOn_two
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:33.340811+00:00
-- url     : https://prove2.me/theorems/71fdb6ab-2dcd-463f-82c5-f82b5989b24a
-- title:
--   Global Theory: continuous On c Hess of cont Diff On two
-- statement:
--   The Global Theory construction uses the continuous On c Hess of cont Diff On two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwo.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOnComplexHessianOfContDiffOnTwo.lean#L44-L51

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

theorem GlobalTheory.continuousOn_cHess_of_contDiffOn_two :
    ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l,
      ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by sorry
