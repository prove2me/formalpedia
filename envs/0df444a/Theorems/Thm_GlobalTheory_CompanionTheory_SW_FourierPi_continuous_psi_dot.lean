-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_continuous_psi_dot
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.continuous_psi_dot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:27.517043+00:00
-- url     : https://prove2.me/theorems/7fb531e7-b869-4afc-a616-dc9c1293e807
-- title:
--   Fourier Pi: continuous psi dot
-- statement:
--   The Fourier Pi construction uses the continuous psi dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L204-L206

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

theorem GlobalTheory.CompanionTheory.SW.FourierPi.continuous_psi_dot (hc : Continuous ψ) {X : Type} [TopologicalSpace X] {f g : X → ι → R}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun p => ψ (f p ⬝ᵥ g p) := by sorry
