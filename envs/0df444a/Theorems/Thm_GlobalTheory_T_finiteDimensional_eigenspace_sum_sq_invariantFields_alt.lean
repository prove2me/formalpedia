-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteDimensional_eigenspace_sum_sq_invariantFields_alt
-- name    : GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:39:23.531471+00:00
-- url     : https://prove2.me/theorems/02125976-b9f2-4e4b-aa4a-a151ef52f3ec
-- title:
--   T: finite Dimensional eigenspace sum sq invariant Fields alt
-- statement:
--   The T construction uses the finite Dimensional eigenspace sum sq invariant Fields alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalEigenspaceSumSqInvariantFieldsAStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FiniteDimensionalEigenspaceSumSqInvariantFieldsAStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalEigenspaceSumSqInvariantFieldsA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteDimensionalEigenspaceSumSqInvariantFieldsAStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteDimensional_eigenspace_sum_sq_invariantFields_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L] (S : Submodule ℂ (K → ℂ)), (∀ f ∈ S, Continuous f) → ∀ e : L → K, (∀ X : L, Continuous fun t : ℝ => e (t • X)) → e 0 = 1 → (∀ r : ℝ, 0 < r → e '' Metric.ball 0 r ∈ 𝓝 (1 : K)) → ∀ d : L → Module.End ℂ S, (∀ X Y, d (X + Y) = d X + d Y) → (∀ (a : ℝ) X, d (a • X) = (a : ℂ) • d X) → (∀ (X : L) (f : S) (x : K) (t : ℝ), HasDerivAt (fun t : ℝ => f.1 (x * e (t • X))) ((d X f).1 (x * e (t • X))) t) → ∀ (ι : Type) [Fintype ι] (X : ι → L), Submodule.span ℝ (Set.range X) = ⊤ → ∀ lam : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (∑ i, d (X i) * d (X i)) lam) := by sorry
