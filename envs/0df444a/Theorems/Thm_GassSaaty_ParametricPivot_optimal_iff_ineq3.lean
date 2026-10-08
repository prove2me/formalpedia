-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_optimal_iff_ineq3
-- name    : GassSaaty.ParametricPivot.optimal_iff_ineq3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:16.272605+00:00
-- url     : https://prove2.me/theorems/69c48b8d-a735-4644-8868-b4549ca2425a
-- title:
--   Case A, (3) — a basic feasible solution is a minimum at $\lambda$ iff $\alpha_j + \lambda\beta_j \le 0$ for all $j$
-- statement:
--   Consider the parametric linear program
--
--   $$
--   \text{minimize } (d + \lambda d')^{\top} x \quad \text{subject to } Ax = b,\ x \ge 0,
--   $$
--
--   with $A$ an $m \times n$ real matrix whose rows are linearly independent, and assume the problem is **nondegenerate**: no basic feasible solution has more than $n - m$ zero components. Let $B$ be a basis with basic feasible solution $x$, and let $\alpha_j + \lambda\beta_j$ be the quantities $z_j - c_j$ of the basis $B$ for the cost $c = d + \lambda d'$. Then, for every real $\lambda$,
--
--   $$
--   x \text{ minimizes } (d + \lambda d')^{\top} x \text{ over } \{x : Ax = b,\ x \ge 0\} \iff \alpha_j + \lambda \beta_j \le 0 \ \ (j = 1, \dots, n). \qquad (3)
--   $$
--
--   The paper writes the forward implication "by the simplex method, this solution will yield the minimum for all $\lambda$ satisfying (3)", and the proof of the THEOREM uses the converse under the standing nondegeneracy assumption ("$\lambda < \bar\lambda$ does not satisfy (3')" is how it shows that the new basis gives no minimum there). Together with the next milestone it gives Summary (3): a solution is a minimum over a closed interval of $\lambda$.
--
--   **Formalization Note** "Yields the minimum" is read as `IsLpOptimal`: $x$ is feasible and its cost is at most the cost of every feasible point. The parameter $\lambda$ is the Lean variable `t` (`λ` is a Lean keyword). Nondegeneracy is the paper's standing assumption of §2, stated as: every basic feasible solution of the standard-form system is nondegenerate (Bertsimas–Tsitsiklis Definition 2.11). Linear independence of the rows of $A$ is required by the platform's optimality criterion; it follows from the existence of a basis of $m$ columns, so it adds nothing to the paper's setting. The reverse implication ((3) ⇒ minimum) holds without nondegeneracy.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 40, Section 2 (standing assumptions) and Case A, Eq. (3)

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem optimal_iff_ineq3 {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x) (t : ℝ) :
    IsLpOptimal (d + t • d') (stdPolyhedron A b) x ↔
      ∀ j, alpha A d B j + t * beta A d' B j ≤ 0 := by sorry

end GassSaaty.ParametricPivot
