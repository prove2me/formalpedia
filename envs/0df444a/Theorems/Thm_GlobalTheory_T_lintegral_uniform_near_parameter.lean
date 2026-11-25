-- Prove2me | Theorems.Thm_GlobalTheory_T_lintegral_uniform_near_parameter
-- name    : GlobalTheory.T.lintegral_uniform_near_parameter
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:16.347806+00:00
-- url     : https://prove2.me/theorems/a72b7e47-fe1b-4fa2-91b2-9301c19e4161
-- title:
--   T: lintegral uniform near parameter
-- statement:
--   The T construction uses the lintegral uniform near parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralUniformNearParameterStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralUniformNearParameterStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameter
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameterStatement
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

theorem GlobalTheory.T.lintegral_uniform_near_parameter : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ → (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) → ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ → ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u → (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) → (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧ ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by sorry
