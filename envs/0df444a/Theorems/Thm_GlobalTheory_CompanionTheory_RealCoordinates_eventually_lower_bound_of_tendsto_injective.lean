-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RealCoordinates_eventually_lower_bound_of_tendsto_injective
-- name    : GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:35.460469+00:00
-- url     : https://prove2.me/theorems/f646b24e-1175-4efc-9839-fdad02aa1dad
-- title:
--   Real Coordinates: eventually lower bound of tendsto injective
-- statement:
--   The Real Coordinates construction uses the eventually lower bound of tendsto injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UniformLowerBoundNearInjective.lean#L7-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UniformLowerBoundNearInjective.lean#L7-L81

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniformLowerBoundNearInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RealCoordinates

theorem GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective
    (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ)
    (e : X ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm) (c : P)
    (A : P → X →+ X) (hA : ∀ s, Continuous (A s))
    (hlim : ∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x)))
    (hinj : Function.Injective (A c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by sorry
