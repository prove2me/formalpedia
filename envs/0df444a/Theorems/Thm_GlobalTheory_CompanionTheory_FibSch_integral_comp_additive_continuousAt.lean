-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FibSch_integral_comp_additive_continuousAt
-- name    : GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:49.768151+00:00
-- url     : https://prove2.me/theorems/538a11bd-aa26-4b1c-8832-89bd2d4e50c4
-- title:
--   Fib Sch: integral comp additive continuous At
-- statement:
--   The Fib Sch construction uses the integral comp additive continuous At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralUniformNearParameter.lean#L17-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralUniformNearParameter.lean#L17-L68

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameter
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibSch

theorem GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt :
    ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
      [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)),
      Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) →
      (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ →
      (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) →
      ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ →
      ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u →
      (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) →
      (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧
        ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by sorry
