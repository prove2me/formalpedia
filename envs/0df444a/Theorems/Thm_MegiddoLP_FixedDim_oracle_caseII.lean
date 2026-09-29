-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_oracle_caseII
-- name    : MegiddoLP.FixedDim.oracle_caseII
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:12:35.343456+00:00
-- url     : https://prove2.me/theorems/691722ab-1498-41e9-aa51-1bdcfbe7e27c
-- title:
--   Oracle, Case II: systems (1) and (2) decide the side of $\{x_d=0\}$ or prove infeasibility (corrected direction)
-- statement:
--   Consider the system $Ax\ge b$ with at least one row, in variables $x_1,\dots,x_d$, and suppose it has no solution with $x_d=0$. Let $f(x)=\max_i(b_i-a_i^Tx)$ be its infeasibility function. Let $x'$ with $x'_d=0$ minimize $f$ over the hyperplane $\{x_d=0\}$, and let $I'=\{i: f(x')=b_i-a_i^Tx'\}$. Consider the systems of the page,
--
--   $$(1)\quad y_d=1,\ \ a_i^Ty\ge0\ (i\in I'),\qquad\qquad (2)\quad z_d=-1,\ \ a_i^Tz\ge0\ (i\in I').$$
--
--   These are $\sum_{j<d}a_{ij}y_j\ge-a_{id}$ and $\sum_{j<d}a_{ij}z_j\ge a_{id}$. Then:
--
--   1. if (1) is feasible, every $w$ with $f(w)<f(x')$ has $w_d>0$;
--   2. if (2) is feasible, every $w$ with $f(w)<f(x')$ has $w_d<0$;
--   3. if (1) and (2) are both feasible or both infeasible, then $x'$ is a global minimum of $f$ and the system $Ax\ge b$ is infeasible.
--
--   So when precisely one of (1), (2) is feasible, the points of smaller infeasibility, and hence any feasible point, lie in one determined open half-space, and the recursion continues there.
--
--   **Formalization Note** (corrected) The page's last sentence reads "if (1) is the feasible one, we proceed into $\{x_d<0\}$". The paragraph before it shows the opposite: if (1) is feasible, the answer to Q2 (improvement in $\{x_d<0\}$) is negative. Parts 1 and 2 state the direction that argument proves. The rows are indexed by `Fin (n + 1)`, so $f$ is a maximum over a nonempty set. The paper's $x_d$ is `Fin.last d` of `Fin (d + 1)`.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §4, p. 125 (Case II, systems (1) and (2))

import Mathlib
import Definitions.Def_Polyhedron
import Definitions.Def_MegiddoLP_FixedDim_Infeasibility

/-!
Megiddo, J. ACM 31 (1984), §4 p. 125, Case II of the oracle. The paper's `x_d` is the last
coordinate `Fin.last d` of `Fin (d + 1)`; the tested hyperplane is `{x_d = 0}`. Systems (1)
and (2) of the page are `∃ y, y_d = 1 ∧ Aᵢ ⬝ᵥ y ≥ 0 (i ∈ I')` and
`∃ z, z_d = -1 ∧ Aᵢ ⬝ᵥ z ≥ 0 (i ∈ I')`. The side is stated in the corrected direction:
(1) feasible puts every point of smaller infeasibility in `{x_d > 0}`.
-/

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

/-- **Oracle, Case II.** Let the system `Ax ≥ b` (at least one row) have no solution on
`{x_d = 0}`, let `x'` with `x'_d = 0` minimize `f = infeas A b` on `{x_d = 0}`, and let
`I' = {i | f(x') = bᵢ - Aᵢ ⬝ᵥ x'}`. Then
1. if (1) is feasible, every `w` with `f(w) < f(x')` has `w_d > 0`;
2. if (2) is feasible, every `w` with `f(w) < f(x')` has `w_d < 0`;
3. if (1) and (2) are both feasible or both infeasible, `x'` minimizes `f` on all of `ℝ^d`
   and `Ax ≥ b` is infeasible. -/
theorem oracle_caseII {n d : ℕ} (A : Matrix (Fin (n + 1)) (Fin (d + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) (x' : Fin (d + 1) → ℝ)
    (hinf : polyhedron A b ∩ {x | x (Fin.last d) = 0} = ∅)
    (hx' : x' (Fin.last d) = 0)
    (hmin : ∀ w : Fin (d + 1) → ℝ, w (Fin.last d) = 0 → infeas A b x' ≤ infeas A b w) :
    ((∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) →
      ∀ w, infeas A b w < infeas A b x' → 0 < w (Fin.last d)) ∧
    ((∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z) →
      ∀ w, infeas A b w < infeas A b x' → w (Fin.last d) < 0) ∧
    (((∃ y : Fin (d + 1) → ℝ, y (Fin.last d) = 1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ y) ↔
      (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        ∀ i, infeas A b x' = b i - A i ⬝ᵥ x' → 0 ≤ A i ⬝ᵥ z)) →
      (∀ w, infeas A b x' ≤ infeas A b w) ∧ polyhedron A b = ∅) := by sorry

end MegiddoLP.FixedDim
