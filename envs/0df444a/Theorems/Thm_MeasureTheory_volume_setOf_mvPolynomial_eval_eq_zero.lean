-- Prove2me | Theorems.Thm_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero
-- name    : MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/8671fde7-43a0-57e7-96b3-1932a7e3d2a8
-- title:
--   Zero sets of non-zero real polynomials are Lebesgue-null
-- statement:
--   Fix a natural number $n$ and a polynomial $p$ in the commutative ring $\mathrm{MvPolynomial}\ (\mathrm{Fin}\ n)\ \mathbb{R}$ of polynomials in $n$ variables indexed by $\mathrm{Fin}\ n$ with real coefficients, and assume $p \neq 0$. The conclusion is that the subset of $\mathrm{Fin}\ n \to \mathbb{R}$, i.e. of $\mathbb{R}^n$, consisting of those $x$ with $\mathrm{eval}\ x\ p = 0$ — the zero locus of $p$ — has measure $0$ for `volume`, the Lebesgue (Haar) measure on the finite product $\mathrm{Fin}\ n \to \mathbb{R}$. Equivalently, $p(x) \neq 0$ for Lebesgue-almost every $x \in \mathbb{R}^n$. The case $n = 0$ is included: there the zero locus of a non-zero constant is empty.
--
--   This is the standard fact that a non-trivial real algebraic hypersurface in $\mathbb{R}^n$ is Lebesgue-null, used to say that an algebraic condition holds almost everywhere. It is invoked in the construction of product measures attached to Gram/trace forms ([`MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq`](thm.html#MeasureTheory.Measure.map_withDensity_gram_trace_matrix_pi_eq_pi_of_span_eq)) and in the archimedean comparison of twisted and ordinary orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_volume_setOf_mvPolynomial_eval_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.volume_setOf_mvPolynomial_eval_eq_zero
    {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by sorry
