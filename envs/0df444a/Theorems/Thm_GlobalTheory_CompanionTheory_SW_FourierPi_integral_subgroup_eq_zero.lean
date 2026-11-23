-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_integral_subgroup_eq_zero
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.integral_subgroup_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:33.81087+00:00
-- url     : https://prove2.me/theorems/0cd8b264-c56d-4269-a835-acf149e16aed
-- title:
--   Fourier Pi: integral subgroup eq zero
-- statement:
--   The Fourier Pi construction uses the integral subgroup eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L57-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L57-L78

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
  {ψ : R → ℂ}

theorem GlobalTheory.CompanionTheory.SW.FourierPi.integral_subgroup_eq_zero (lam : Measure R) [lam.IsAddHaarMeasure] (A : AddSubgroup R)
    (hA : MeasurableSet (A : Set R)) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (t a : R) (haA : a ∈ A)
    (hne : ψ (a * t) ≠ 1) : ∫ x in (A : Set R), ψ (x * t) ∂lam = 0 := by sorry
