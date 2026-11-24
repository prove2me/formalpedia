-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_fubini_box
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.fubini_box
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:15.546351+00:00
-- url     : https://prove2.me/theorems/da3b899b-c06b-4fc0-875c-f5ea10dea5c0
-- title:
--   Fourier Pi: fubini box
-- statement:
--   The Fourier Pi construction uses the fubini box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L208-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L208-L229

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ} {ι : Type} [Fintype ι]

theorem GlobalTheory.CompanionTheory.SW.FourierPi.fubini_box (hc : Continuous ψ) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (μ : Measure (ι → R)) [SFinite μ] (B : Set (ι → R)) (hBf : μ B < ⊤) (Φ : (ι → R) → ℂ)
    (Φc : Continuous Φ) (hi : Integrable Φ μ) (z : ι → R) :
    ∫ y in B, (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ z) ∂μ =
      ∫ x, Φ x * ∫ y in B, ψ ((x + z) ⬝ᵥ y) ∂μ ∂μ := by sorry
