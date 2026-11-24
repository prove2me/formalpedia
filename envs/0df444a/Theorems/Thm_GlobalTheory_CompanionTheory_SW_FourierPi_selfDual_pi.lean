-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FourierPi_selfDual_pi
-- name    : GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:38.819461+00:00
-- url     : https://prove2.me/theorems/b650b498-96ea-4b7f-a406-3a13a4cb4e3e
-- title:
--   Fourier Pi: self Dual pi
-- statement:
--   The Fourier Pi construction uses the self Dual pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L293-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HarrisTaylorCardKilledByIdealEqAbsNormPow.lean#L293-L373

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

theorem GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ψ : R → ℂ), Continuous ψ → (∀ x y, ψ (x + y) = ψ x * ψ y) → (∀ x, ‖ψ x‖ = 1) → ∀ lam : Measure R, SelfDual lam (fun s t => ψ (s * t)) → (∃ L : AddSubgroup R, IsCompact (L : Set R) ∧ IsOpen (L : Set R)) → (∀ L : AddSubgroup R, IsCompact (L : Set R) → IsOpen (L : Set R) → IsCompact {t | ∀ s ∈ L, ψ (s * t) = 1}) → (∀ K : Set R, IsCompact K → ∃ L : AddSubgroup R, IsCompact (L : Set R) ∧ IsOpen (L : Set R) ∧ K ⊆ L) → (∀ U ∈ 𝓝 (0 : R), ∃ L : AddSubgroup R, IsCompact (L : Set R) ∧ IsOpen (L : Set R) ∧ (L : Set R) ⊆ U) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => lam) (fun x y => ψ (x ⬝ᵥ y)) := by sorry
