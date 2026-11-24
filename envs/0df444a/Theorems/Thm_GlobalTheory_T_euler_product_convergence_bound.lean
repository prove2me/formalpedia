-- Prove2me | Theorems.Thm_GlobalTheory_T_euler_product_convergence_bound
-- name    : GlobalTheory.T.euler_product_convergence_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:50.192544+00:00
-- url     : https://prove2.me/theorems/31df6928-c241-4586-a44e-1c40e9b9925c
-- title:
--   T: euler product convergence bound
-- statement:
--   The T construction uses the euler product convergence bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EulerProductConvergenceBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EulerProductConvergenceBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.euler_product_convergence_bound : CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (K : Set (Ainf F)), IsCompact K → ∀ N : ℕ, 0 < N → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), 0 ≤ C → (∀ v, v ∉ S → (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧ ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) → ∀ δ : ℝ, 0 < δ → ∀ D : Finset (HeightOneSpectrum (𝓞 F)), Disjoint D S → ∀ B : Finset F, (∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ (∃ y : 𝓞 F, (y : F) = (N : F) * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K) → δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤ C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by sorry
