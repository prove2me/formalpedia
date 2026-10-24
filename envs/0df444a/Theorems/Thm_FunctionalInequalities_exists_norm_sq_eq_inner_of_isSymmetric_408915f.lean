-- Prove2me | Theorems.Thm_FunctionalInequalities_exists_norm_sq_eq_inner_of_isSymmetric_408915f
-- name    : FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:11.925343+00:00
-- url     : https://prove2.me/theorems/4c50ec41-cbbe-452e-a877-aa390cb79d3c
-- title:
--   Norm Factorization of a Positive Symmetric Quadratic Form
-- statement:
--   This constructs a norm factor for a positive symmetric operator.
--
--   Let $V$ be a finite-dimensional real inner-product space and let $T:V\to V$ be a continuous linear map. Assume:
--
--   1. $T$ is symmetric;
--   2. its quadratic form is nonnegative:
--
--   $$
--   0\le\langle Tv,v\rangle\qquad\text{for every }v\in V.
--   $$
--
--   Then there exists a continuous linear map $B:V\to V$ such that
--
--   $$
--   \langle Tv,v\rangle=\|Bv\|^2
--   \qquad\text{for every }v\in V.
--   $$
--
--   Only existence of $B$ is asserted; it need not be stated symmetric, unique, or positive.
--
--   The result provides the abstract square-root-type factorization used to represent covariance energies by weighted gradients.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Factorization.lean#L31-L65 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Factorization`, declaration `FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.exists_norm_sq_eq_inner_of_isSymmetric_408915f (T : V →L[ℝ] V)
    (hT : T.toLinearMap.IsSymmetric) (hpos : ∀ v, 0 ≤ inner ℝ (T v) v) :
    ∃ B : V →L[ℝ] V, ∀ v, inner ℝ (T v) v = ‖B v‖ ^ 2 := by sorry
