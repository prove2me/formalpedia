-- Prove2me | Theorems.Thm_GlobalTheory_T_universal_coefficient_degree_zero
-- name    : GlobalTheory.T.universal_coefficient_degree_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:11.15996+00:00
-- url     : https://prove2.me/theorems/49a06de0-11c3-4691-99eb-6ad2e3c9b85b
-- title:
--   T: universal coefficient degree zero
-- statement:
--   The T construction uses the universal coefficient degree zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UniversalCoefficientDegreeZeroStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UniversalCoefficientDegreeZeroStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.universal_coefficient_degree_zero : ∀ (R A₀ A₁ P₀ P₁ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] (d₀ : A₀ →ₗ[R] A₁) (a₀ : P₀ →ₗ[R] P₁) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (e : A₀), ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → d₀ e = 0 → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] A₀) (d₀.lTensor M) (ψ₀.lTensor M)) → (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x) → ∃ u : P₀, a₀ u = 0 ∧ ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧ ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x := by sorry
