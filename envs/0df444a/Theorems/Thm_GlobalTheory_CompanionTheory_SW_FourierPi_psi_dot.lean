-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_psi_dot
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.psi_dot
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:01.051389+00:00
-- url     : https://prove2.me/theorems/70a8af41-0cfa-4b44-9be6-f3f9ac612c96
-- title:
--   Fourier Pi: psi dot
-- statement:
--   The Fourier Pi construction uses the psi dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L30-L32

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

theorem GlobalTheory.CompanionTheory.SW.FourierPi.psi_dot (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (hn : ∀ x, ‖ψ x‖ = 1) {ι : Type} [Fintype ι]
    (x y : ι → R) : ψ (x ⬝ᵥ y) = ∏ i, ψ (x i * y i) := by sorry
