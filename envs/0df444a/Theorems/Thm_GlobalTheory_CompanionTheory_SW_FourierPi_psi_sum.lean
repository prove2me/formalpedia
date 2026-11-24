-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_psi_sum
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.psi_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:17.153203+00:00
-- url     : https://prove2.me/theorems/a8a75dac-2074-4e2f-93d6-183a6b5d3aaa
-- title:
--   Fourier Pi: psi sum
-- statement:
--   The Fourier Pi construction uses the psi sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L23-L28

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
variable {R : Type} [CommRing R] {ψ : R → ℂ}

theorem GlobalTheory.CompanionTheory.SW.FourierPi.psi_sum (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type}
    (s : Finset ι) (f : ι → R) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by sorry
