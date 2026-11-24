-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_ann_eq
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.integral_ann_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:20.57183+00:00
-- url     : https://prove2.me/theorems/6e420772-3ce8-4516-928e-230be70d3d1f
-- title:
--   Fourier Pi: integral ann eq
-- statement:
--   The Fourier Pi construction uses the integral ann eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L163-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L163-L179

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
open Classical

theorem GlobalTheory.CompanionTheory.SW.FourierPi.integral_ann_eq (lam : Measure R) [lam.IsAddHaarMeasure] (L P : AddSubgroup R)
    (hPm : MeasurableSet (P : Set R)) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y)
    (hLP : ∀ s ∈ L, ∀ t ∈ P, ψ (s * t) = 1) (hPL : ∀ z, (∀ t ∈ P, ψ (t * z) = 1) → z ∈ L) (s : R) :
    ∫ t in (P : Set R), ψ (s * t) ∂lam = if s ∈ L then (lam.real (P : Set R) : ℂ) else 0 := by sorry
