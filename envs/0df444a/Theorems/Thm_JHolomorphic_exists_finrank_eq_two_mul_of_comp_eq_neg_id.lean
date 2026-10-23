-- Prove2me | Theorems.Thm_JHolomorphic_exists_finrank_eq_two_mul_of_comp_eq_neg_id
-- name    : JHolomorphic.exists_finrank_eq_two_mul_of_comp_eq_neg_id
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T14:34:51.120477+00:00
-- url     : https://prove2.me/theorems/4e66e9c6-4c3d-41b0-9edd-5770eec55434
-- title:
--   A real space with a linear complex structure has even dimension
-- statement:
--   Let $E$ be a finite-dimensional real normed vector space and let $J:E\to E$ be a continuous real-linear map with $J\circ J=-\mathrm{Id}_E$. Then $\dim_{\mathbb{R}}E$ is even: there is a natural number $n$ with $\dim_{\mathbb{R}}E=2n$.
--
--   This supplies the complex dimension $n$ needed to compare $E$ with $\mathbb{C}^n$ whenever $E$ carries a linear complex structure, for instance the value of an almost complex structure at one point.
--
--   **Formalization Note** The hypothesis is `J.comp J = -ContinuousLinearMap.id ℝ E` for `J : E →L[ℝ] E`; the conclusion is `∃ n : ℕ, Module.finrank ℝ E = 2 * n`. The case $E=\{0\}$ (with $n=0$) is included.
-- source:
--   Standard linear algebra; used in C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2

import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace JHolomorphic

/-- A finite-dimensional real normed space carrying a continuous linear map `J` with
`J ∘ J = -1` has even real dimension. -/
theorem exists_finrank_eq_two_mul_of_comp_eq_neg_id {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E →L[ℝ] E)
    (hJ : J.comp J = -ContinuousLinearMap.id ℝ E) :
    ∃ n : ℕ, Module.finrank ℝ E = 2 * n := by
  sorry

end JHolomorphic
