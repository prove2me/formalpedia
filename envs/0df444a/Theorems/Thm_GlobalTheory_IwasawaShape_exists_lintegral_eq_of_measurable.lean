-- Prove2me | Theorems.Thm_GlobalTheory_IwasawaShape_exists_lintegral_eq_of_measurable
-- name    : GlobalTheory.IwasawaShape.exists_lintegral_eq_of_measurable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:37.159969+00:00
-- url     : https://prove2.me/theorems/6679999c-3d03-4480-be63-66443c49baae
-- title:
--   Iwasawa Shape: exists lintegral eq of measurable
-- statement:
--   The Iwasawa Shape construction uses the exists lintegral eq of measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLintegralEqOfMeasurable.lean#L12-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLintegralEqOfMeasurable.lean#L12-L206

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.IwasawaShape.exists_lintegral_eq_of_measurable (N M K : Subgroup G) (hN : IsClosed (N : Set G))
    (hM : IsClosed (M : Set G)) (hK : IsCompact (K : Set G)) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (huniq : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) (hdec : ∀ g, ∃ u ∈ N, ∃ m ∈ M, ∃ k ∈ K, g = u * m * k)
    (μ μN μM μK : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0)
    [IsFiniteMeasureOnCompacts μN] [IsFiniteMeasureOnCompacts μM] [IsProbabilityMeasure μK]
    (C : Set G) (hC : IsCompact C) (hC0 : μN C ≠ 0) (hM0 : μM ≠ 0)
    (h1 : μN (N : Set G)ᶜ = 0) (h2 : μM (M : Set G)ᶜ = 0)
    (iN : ∀ s ∈ N, μN.map (fun g => s * g) = μN) (iM : ∀ s ∈ M, μM.map (fun g => s * g) = μM)
    (iK : ∀ s ∈ K, μK.map (fun g => s * g) = μK) (δ : G → ENNReal) (hδ : Measurable δ)
    (hmod : ∀ m ∈ M, μN.map (fun u => m * u * m⁻¹) = δ m • μN) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN := by sorry
