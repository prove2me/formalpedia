-- Prove2me | Theorems.Thm_GlobalTheory_le_mul_setIntegral_image2_of_forall_le
-- name    : GlobalTheory.le_mul_setIntegral_image2_of_forall_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:14.587662+00:00
-- url     : https://prove2.me/theorems/b8047f95-1617-432b-9365-042824dd7f0d
-- title:
--   Global Theory: le mul set Integral image2 of forall le
-- statement:
--   The Global Theory construction uses the le mul set Integral image2 of forall le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeMulSetIntegralImage2OfForallLe.lean#L6-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeMulSetIntegralImage2OfForallLe.lean#L6-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeMulSetIntegralImage2OfForallLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.le_mul_setIntegral_image2_of_forall_le (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ)
    (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ)
    (hΘ : Continuous Θ) (hQ : IsCompact Q) (hB : IsCompact B) (hB1 : B ∈ nhds (1 : G))
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) →
      (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) →
      a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by sorry
