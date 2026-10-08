-- Prove2me | Theorems.Thm_MifflinSemismooth_Optimality_theorem9
-- name    : MifflinSemismooth.Optimality.theorem9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:10.952025+00:00
-- url     : https://prove2.me/theorems/e31be100-2b28-475b-ae98-f56b68ff7442
-- title:
--   Theorem 9, p. 20 — f, h semiconvex and 0 ∈ M(x̄): no feasible point, or x̄ optimal, or no strictly feasible point
-- statement:
--   Consider the problem of minimizing $f(x)$ subject to $h(x)\le 0$, with $f,h:\mathbb R^n\to\mathbb R$, and the map $M$ of §5 ($M(x)=\partial f(x)$ if $h(x)<0$, $\operatorname{conv}\{\partial f(x)\cup\partial h(x)\}$ if $h(x)=0$, $\partial h(x)$ if $h(x)>0$). Suppose $f$ and $h$ are semiconvex on $\mathbb R^n$ and $\bar x\in\mathbb R^n$ satisfies $0\in M(\bar x)$.
--
--   1. If $h(\bar x)>0$, then $h(x)\ge h(\bar x)>0$ for all $x\in\mathbb R^n$; that is, the problem has no feasible points.
--   2. If $h(\bar x)\le 0$, then at least one of the following holds:
--      - (i) $\bar x$ is optimal;
--      - (ii) $h(x)\ge 0$ for all $x\in\mathbb R^n$; that is, the problem has no strictly feasible points.
--
--   In formulas:
--   $$
--   \bigl(h(\bar x)>0\Rightarrow \forall x,\ h(x)\ge h(\bar x)>0\bigr)\ \wedge\ \bigl(h(\bar x)\le 0\Rightarrow \bar x\ \text{optimal}\ \vee\ \forall x,\ h(x)\ge 0\bigr).
--   $$
--
--   Together with Theorem 7 (optimality implies stationarity) this says that for semiconvex problem functions with a strictly feasible point (a Slater-type condition), stationarity is equivalent to optimality. It is the nonsmooth analogue of the classical sufficiency of the Karush–Kuhn–Tucker conditions for pseudoconvex objective and quasiconvex constraints.
--
--   **Formalization Note** "Semiconvex on $\mathbb R^n$" is semiconvexity at each point with respect to $X=\mathbb R^n$. The hypothesis is $0\in M(\bar x)$ alone, without feasibility, since case 1 concerns infeasible $\bar x$. The theorem is stated for an arbitrary constraint function $h$; the paper's $h=\max_i h_i$ is a special case, and Theorem 6 transfers semiconvexity from the $h_i$ to $h$.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 20, Theorem 9

import Mathlib
import Definitions.Def_MifflinSemismooth_Optimality_Setting

namespace MifflinSemismooth.Optimality

/-- Mifflin (1976), §5, Theorem 9, p. 20: if `f` and `h` are semiconvex on `ℝⁿ` and `0 ∈ M(x̄)`,
then (a) `h(x̄) > 0` implies `h(x) ≥ h(x̄) > 0` for all `x`; (b) `h(x̄) ≤ 0` implies that `x̄` is
optimal or `h(x) ≥ 0` for all `x`. -/
theorem theorem9 {n : ℕ} (f h : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MifflinSemismooth.Extremal.SemiconvexOn Set.univ f)
    (hh : MifflinSemismooth.Extremal.SemiconvexOn Set.univ h) (xbar : EuclideanSpace ℝ (Fin n))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ Mmap f h xbar) :
    (0 < h xbar → ∀ x, h xbar ≤ h x ∧ 0 < h x) ∧
      (h xbar ≤ 0 → IsOptimal f h xbar ∨ ∀ x, 0 ≤ h x) := by sorry

end MifflinSemismooth.Optimality
