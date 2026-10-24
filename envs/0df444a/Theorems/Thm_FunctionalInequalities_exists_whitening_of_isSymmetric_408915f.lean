-- Prove2me | Theorems.Thm_FunctionalInequalities_exists_whitening_of_isSymmetric_408915f
-- name    : FunctionalInequalities.exists_whitening_of_isSymmetric_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:30.796576+00:00
-- url     : https://prove2.me/theorems/13843a48-b111-4185-948c-cde495a8acbc
-- title:
--   Whitening Equivalence for Positive Definite Symmetric Operators
-- statement:
--   This is a finite-dimensional whitening existence theorem.
--
--   Let $V$ be a finite-dimensional real inner-product normed space and let $T:V\to V$ be continuous linear. Assume:
--
--   1. $T$ is symmetric;
--   2. $\langle Tv,v\rangle>0$ for every nonzero $v\in V$.
--
--   Then there exists a continuous linear equivalence $W:V\simeq V$ such that $W$ is self-adjoint and
--
--   $$\langle T(Wu),Wv\rangle=\langle u,v\rangle\qquad\text{for all }u,v\in V.$$
--
--   Only existence of a self-adjoint whitening equivalence is asserted; positivity or uniqueness of $W$ is not part of the conclusion.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Whitening.lean#L42-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Whitening`, declaration `FunctionalInequalities.exists_whitening_of_isSymmetric`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.exists_whitening_of_isSymmetric_408915f (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ (T v) v) :
    ∃ W : V ≃L[ℝ] V, (W : V →L[ℝ] V).adjoint = W ∧
      ∀ u v, inner ℝ (T (W u)) (W v) = inner ℝ u v := by sorry
