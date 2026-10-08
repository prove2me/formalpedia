-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_theorem_new_basis_interval_starts_at_lambdaBar
-- name    : GassSaaty.ParametricPivot.theorem_new_basis_interval_starts_at_lambdaBar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:41.28996+00:00
-- url     : https://prove2.me/theorems/120ca518-a2c2-4d49-bfbc-f482cf120b9d
-- title:
--   THEOREM (Gass–Saaty) — the basis entered at $\bar\lambda$ yields a minimum, and the least such $\lambda$ is $\bar\lambda$
-- statement:
--   Consider the parametric linear program of Gass and Saaty,
--
--   $$
--   \text{minimize } \sum_{j=1}^n (d_j + \lambda d'_j)\, x_j \quad \text{subject to } x_j \ge 0,\ \ \sum_{j=1}^n a_{ij} x_j = a_{i0}\ (i = 1, \dots, m),
--   $$
--
--   where the rows of $A = (a_{ij})$ are linearly independent and the problem is nondegenerate (no basic feasible solution has more than $n - m$ zero components). Let $B$ be a basis with basic feasible solution $x$, and write $z_j - c_j = \alpha_j + \lambda\beta_j$ for this basis. Assume:
--
--   1. (Case A) the inequalities $\alpha_j + \lambda\beta_j \le 0$, $j = 1, \dots, n$, are consistent;
--   2. $s$ is an index with $\beta_s > 0$ attaining $\bar\lambda = \min_{\beta_j > 0}(-\alpha_j/\beta_j) = -\alpha_s/\beta_s$ (so $\bar\lambda$ is finite);
--   3. $r = B(\ell)$ is a basic column with $y_{rs} > 0$ chosen by the simplex ratio test: $x_r / y_{rs} \le x_{B(i)} / y_{is}$ for every $i$ with $y_{is} > 0$;
--   4. $B'$ is the basis obtained by bringing $A_s$ in and taking $A_r$ out, and $x' = x + (x_r / y_{rs})\, d^{(s)}$, with $d^{(s)}$ the $s$-th basic direction, is its basic solution.
--
--   Then $\bar\lambda$ is the least $\lambda$ for which $x'$ minimizes the cost:
--
--   $$
--   \bar\lambda = \min \big\{ \lambda \in \mathbb R : x' \text{ minimizes } (d + \lambda d')^{\top} x \text{ over } \{x : Ax = b,\ x \ge 0\} \big\}.
--   $$
--
--   The paper's THEOREM reads: "The new basis yields a minimum for at least one value of $\lambda$. If $\underline\lambda' \le \lambda \le \bar\lambda'$ is the entire set of values of $\lambda$ for which the new basis yields a minimum, then $\underline\lambda' = \bar\lambda$." The displayed statement contains both sentences: $\bar\lambda$ belongs to the set, and nothing smaller does. This is what makes the parametric procedure move from one interval of optimality to the next without a gap: the new basis takes over exactly where the old one stops.
--
--   **Formalization Note** "Yields a minimum" is `IsLpOptimal` of the new basic solution over the whole feasible set; "least" is Mathlib's `IsLeast`, so the statement does not presuppose that the set is an interval (that is the milestone on (3)–(5)). $\lambda$ is the Lean variable `t`; $\bar\lambda$ is the real number $-\alpha_s/\beta_s$ with $s$ attaining the minimum in (5), which is the paper's finite case ("Assume then that $\bar\lambda$ is finite, $\bar\lambda = -\alpha_s/\beta_s$, $\beta_s > 0$"). Ties in the minimum and in the ratio test are allowed. Nondegeneracy is stated for every basic feasible solution, as in the paper's standing assumption; linear independence of the rows is implied by the existence of a basis and is required by the platform's criteria. The coordinates $y_{is}$ are `pivotColumn A B s i`, $\alpha, \beta$ are the negatives of the platform's reduced costs, and indices are 0-based. The proof printed in the paper contains a slip in (8) (see the corresponding milestone); the theorem itself is correct.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 41, THEOREM (with the standing assumptions of Section 2, p. 40, and Eqs. (5), (6))

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem theorem_new_basis_interval_starts_at_lambdaBar {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B B' : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (ℓ : Fin m) (hℓ : 0 < pivotColumn A B s ℓ)
    (hratio : ∀ i, 0 < pivotColumn A B s i →
      x (B ℓ) / pivotColumn A B s ℓ ≤ x (B i) / pivotColumn A B s i)
    (hB'ℓ : B' ℓ = s) (hB'ne : ∀ i, i ≠ ℓ → B' i = B i) :
    IsLeast
      {t : ℝ | IsLpOptimal (d + t • d') (stdPolyhedron A b)
        (x + (x (B ℓ) / pivotColumn A B s ℓ) • basicDirection A B s)}
      (-alpha A d B s / beta A d' B s) := by sorry

end GassSaaty.ParametricPivot
