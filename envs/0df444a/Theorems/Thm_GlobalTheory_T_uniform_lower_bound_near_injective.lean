-- Prove2me | Theorems.Thm_GlobalTheory_T_uniform_lower_bound_near_injective
-- name    : GlobalTheory.T.uniform_lower_bound_near_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:09.722491+00:00
-- url     : https://prove2.me/theorems/33194643-38c3-5fe4-8770-aa6d33e31482
-- title:
--   T: uniform lower bound near injective
-- statement:
--   The T construction uses the uniform lower bound near injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UniformLowerBoundNearInjectiveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UniformLowerBoundNearInjectiveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniformLowerBoundNearInjective
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniformLowerBoundNearInjectiveStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.uniform_lower_bound_near_injective : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by sorry
