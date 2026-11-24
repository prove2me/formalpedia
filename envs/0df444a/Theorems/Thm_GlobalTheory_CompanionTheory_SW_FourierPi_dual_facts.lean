-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_dual_facts
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.dual_facts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:34.025118+00:00
-- url     : https://prove2.me/theorems/edd9e38f-447a-4848-a8c5-f5bfe7982642
-- title:
--   Fourier Pi: dual facts
-- statement:
--   The Fourier Pi construction uses the dual facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L85-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L85-L149

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

theorem GlobalTheory.CompanionTheory.SW.FourierPi.dual_facts (hc : Continuous ψ) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1)
    (lam : Measure R) (hsd : SelfDual lam (fun s t => ψ (s * t))) (L : AddSubgroup R)
    (hLc : IsCompact (L : Set R)) (hLo : IsOpen (L : Set R))
    (hP : IsCompact (ann ha hn L : Set R)) :
    lam.real (L : Set R) * lam.real (ann ha hn L : Set R) = 1 ∧
      (∀ z, z ∈ ann ha hn (ann ha hn L) → z ∈ L) ∧ IsOpen (ann ha hn L : Set R) := by sorry
