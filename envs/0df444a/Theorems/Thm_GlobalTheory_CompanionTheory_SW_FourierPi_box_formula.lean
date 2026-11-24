-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_box_formula
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.box_formula
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:32.003804+00:00
-- url     : https://prove2.me/theorems/508912b3-15c7-497f-bcaf-999e37f2024e
-- title:
--   Fourier Pi: box formula
-- statement:
--   The Fourier Pi construction uses the box formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L231-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L231-L258

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

theorem GlobalTheory.CompanionTheory.SW.FourierPi.box_formula (hc : Continuous ψ) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (lam : Measure R) [lam.IsAddHaarMeasure] [SigmaFinite lam] (L P : AddSubgroup R)
    (hLm : MeasurableSet (L : Set R)) (hPm : MeasurableSet (P : Set R)) (hPf : lam (P : Set R) < ⊤)
    (hLP : ∀ s ∈ L, ∀ t ∈ P, ψ (s * t) = 1) (hPL : ∀ z, (∀ t ∈ P, ψ (t * z) = 1) → z ∈ L)
    (Φ : (ι → R) → ℂ) (Φc : Continuous Φ) (hi : Integrable Φ (Measure.pi fun _ : ι => lam))
    (z : ι → R) :
    ∫ y in box ι (P : Set R), (∫ x, Φ x * ψ (x ⬝ᵥ y) ∂(Measure.pi fun _ : ι => lam)) * ψ (y ⬝ᵥ z)
        ∂(Measure.pi fun _ : ι => lam) =
      (lam.real (P : Set R) : ℂ) ^ Fintype.card ι *
        ∫ u in box ι (L : Set R), Φ (u - z) ∂(Measure.pi fun _ : ι => lam) := by sorry
