-- Prove2me | Theorems.Thm_OblivEllipsoid_Infeas_proposition_4_1_b
-- name    : OblivEllipsoid.Infeas.proposition_4_1_b
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T08:39:45.441015+00:00
-- url     : https://prove2.me/theorems/8797ef3c-70c7-4f13-ab6d-cec672513e16
-- title:
--   Proposition 4.1(b) — for infeasible (P), $\tau(A,u)=-z^*>0$ is the least uniform relaxation
-- statement:
--   Let $A=[a_1,\dots,a_m]\in\mathbb R^{n\times m}$ satisfy Assumption 1.1 (the columns positively span $\mathbb R^n$ and have unit Euclidean norm), let $u\in\mathbb R^m$, and define
--
--   $$z^*=\sup_{x\in\mathbb R^n}\ \min_{i\in[m]}\,(u_i-a_i^\top x),\qquad \tau(A,u)=|z^*|.$$
--
--   If the system $(P)$: $A^\top x\le u$ is infeasible, then
--
--   1. $\tau(A,u)=-z^*$;
--   2. $\tau(A,u)>0$;
--   3. $\tau(A,u)$ is the smallest scalar $\theta$ for which the right-hand-side perturbed system $A^\top x\le u+\theta e$ has a feasible solution.
--
--   This is the condition-measure fact behind the iteration bound of the oblivious ellipsoid algorithm on infeasible systems: every point violates some constraint by at least $\tau(A,u)$, and the logarithm of $1/\tau(A,u)$ appears in the bound of Theorem 7.1.
--
--   **Formalization Note** $z^*$ is the platform definition `zStar` (a `sSup` over the range of $x\mapsto\min_i(u_i-a_i^\top x)$), and $e$ is the all-ones vector.
-- source:
--   Lamperski, Freund & Todd, An Oblivious Ellipsoid Algorithm for Solving a System of (In)Feasible Linear Inequalities, arXiv:1910.03114v5, p. 14, Proposition 4.1(b) (with the definition (15) of $z^*$ and $\tau(A,u)$)

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas

/-- Proposition 4.1(b), p. 14. -/
theorem proposition_4_1_b {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin m → ℝ) (hA : Assumption11 A)
    (hinf : ¬ ∃ x : Fin n → ℝ, IsFeasible A u x) :
    tau A u = - zStar A u ∧ 0 < tau A u ∧
      IsLeast {θ : ℝ | ∃ x : Fin n → ℝ, IsFeasible A (u + fun _ => θ) x} (tau A u) := by sorry

end OblivEllipsoid.Infeas
