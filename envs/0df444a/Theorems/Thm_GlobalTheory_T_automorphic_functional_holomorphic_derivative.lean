-- Prove2me | Theorems.Thm_GlobalTheory_T_automorphic_functional_holomorphic_derivative
-- name    : GlobalTheory.T.automorphic_functional_holomorphic_derivative
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:38.163713+00:00
-- url     : https://prove2.me/theorems/0748e971-4ffc-4146-abdc-9042a17ff597
-- title:
--   T: automorphic functional holomorphic derivative
-- statement:
--   The T construction uses the automorphic functional holomorphic derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AutomorphicFunctionalHolomorphicDerivativeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AutomorphicFunctionalHolomorphicDerivativeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivativeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.automorphic_functional_holomorphic_derivative : ∀ {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (Lf : (G → ℂ) → ℂ), (∀ (a : ℂ) (f f' : G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ γ ∈ Γ, ∀ g, f' (γ * g) = f' g) → Lf (a • f + f') = a * Lf f + Lf f') → (∃ C : Set G, IsCompact C ∧ ∀ (f : G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → (∀ x ∈ C, ‖f x‖ ≤ M) → ‖Lf f‖ ≤ M) → ∀ (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → (∀ z ∈ U, ∀ γ ∈ Γ, ∀ g, Ê z (γ * g) = Ê z g) → DifferentiableOn ℂ (fun z => Lf (Ê z)) U ∧ ∀ z ∈ U, ∀ j : ℕ, iteratedDeriv j (fun z => Lf (Ê z)) z = Lf fun g => iteratedDeriv j (Ê · g) z := by sorry
