-- Prove2me | Theorems.Thm_GlobalTheory_NAK_lintegral_eq_nak
-- name    : GlobalTheory.NAK.lintegral_eq_nak
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:04.931453+00:00
-- url     : https://prove2.me/theorems/837e2ee9-4695-50ae-b6bb-78be9a636698
-- title:
--   NAK: lintegral eq nak
-- statement:
--   The NAK construction uses the lintegral eq nak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureIwasawaQuotient.lean#L144-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureIwasawaQuotient.lean#L144-L255

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureIwasawaQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace GroundTheory.Automorphic.HaarSK
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.NAK

theorem GlobalTheory.NAK.lintegral_eq_nak : ∀ (G Λ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [Group Λ] [TopologicalSpace Λ] [IsTopologicalGroup Λ] [LocallyCompactSpace Λ]
    [SecondCountableTopology Λ] [T2Space Λ] [MeasurableSpace Λ] [BorelSpace Λ]
    (N K : Subgroup G) (j : Λ →* G) (δ : Λ →* ℝ≥0) (μG : Measure G) (μN : Measure N) (μK : Measure K) (μΛ : Measure Λ),
    μG.IsHaarMeasure → μN.IsHaarMeasure → μK.IsHaarMeasure → μΛ.IsHaarMeasure →
    IsCompact (K : Set G) → Continuous j → Continuous δ →
    (∀ x, ∀ n ∈ N, j x * n * (j x)⁻¹ ∈ N) →
    IsClosedEmbedding (fun p : N × Λ => (p.1 : G) * j p.2) →
    (∀ x (f : G → ℝ≥0∞), Measurable f → ∫⁻ n, f (j x * n.1 * (j x)⁻¹) ∂μN = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ * ∫⁻ n, f n.1 ∂μN) →
    (∀ g, ∃ n ∈ N, ∃ x, ∃ k ∈ K, g = n * j x * k) →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ x, ∫⁻ n, φ (n.1 * j x * k.1) * ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂μN ∂μΛ ∂μK := by sorry
