-- Prove2me | Theorems.Thm_GlobalTheory_T_le_mul_setIntegral_image2_of_forall_le_alt
-- name    : GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:20.666304+00:00
-- url     : https://prove2.me/theorems/6d4adc52-0fb7-4a43-a18c-3f1d13376628
-- title:
--   T: le mul set Integral image2 of forall le alt
-- statement:
--   The T construction uses the le mul set Integral image2 of forall le alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeMulSetIntegralImage2OfForallLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeMulSetIntegralImage2OfForallLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeMulSetIntegralImage2OfForallLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeMulSetIntegralImage2OfForallLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ) (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ), Continuous Θ → IsCompact Q → IsCompact B → B ∈ nhds (1 : G) → 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) → (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) → a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by sorry
