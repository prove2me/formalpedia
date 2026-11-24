-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_mean_close
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.mean_close
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:48.352308+00:00
-- url     : https://prove2.me/theorems/b3e9922f-3cde-4ec8-bd49-7ca8acb0f01c
-- title:
--   Fourier Pi: mean close
-- statement:
--   The Fourier Pi construction uses the mean close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L260-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L260-L287

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

theorem GlobalTheory.CompanionTheory.SW.FourierPi.mean_close (lam : Measure R) [lam.IsAddHaarMeasure] [SigmaFinite lam] (A : Set R)
    (hAm : MeasurableSet A) (hAf : lam A < ⊤) (c : ℝ) (hc0 : 0 ≤ c) (hcm : lam.real A * c = 1)
    (f : (ι → R) → ℂ) (hf : IntegrableOn f (box ι A) (Measure.pi fun _ : ι => lam)) (v : ℂ) (ε : ℝ)
    (h : ∀ u ∈ box ι A, ‖f u - v‖ ≤ ε) :
    ‖(c : ℂ) ^ Fintype.card ι * ∫ u in box ι A, f u ∂(Measure.pi fun _ : ι => lam) - v‖ ≤ ε := by sorry
