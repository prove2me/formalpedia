-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_nesterov_ye
-- name    : ModernConvex.Relaxations.nesterov_ye
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:57.305084+00:00
-- url     : https://prove2.me/theorems/1f2ce964-efa1-417c-96d9-c1802eb1b0bf
-- title:
--   Proposition 4.10.5 — (Nesterov, Ye) F∗ ≤ (π/2) f∗ for commuting Bᵢ and A ⪰ 0
-- statement:
--   Consider the setting (SL.??): symmetric $n\times n$ matrices $B_1, \dots, B_m$, numbers $d_1, \dots, d_m \ge 0$, the system $(S')$: $x^TB_ix \le d_i$, $i = 1, \dots, m$, and $f(x) = x^TAx$. Let $f^*$ be the optimal value of $(P)\ \max_x\{x^TAx : x^TB_ix \le d_i\}$, $F^*$ the optimal value of
--   $$(SDP)\qquad \max_X\{\operatorname{Tr}(AX) : \operatorname{Tr}(B_iX) \le d_i,\ i = 1,\dots,m,\ X = X^T \succeq 0\},$$
--   and $(SDD)$ the problem $\min_\lambda\{\sum_i\lambda_id_i : \sum_i\lambda_iB_i \succeq A,\ \lambda \ge 0\}$. Assume that
--
--   1. the matrices $B_1, \dots, B_m$ commute with each other;
--   2. system $(S')$ is strictly feasible, and there exists a combination of the matrices $B_i$ with nonnegative coefficients which is positive definite;
--   3. $A \succeq 0$.
--
--   Then $f^* \ge 0$, $(SDD)$ is solvable with the optimal value $F^*$, and
--   $$F^* \le \frac{\pi}{2}\,f^*. \qquad (4.10.137)$$
--
--   This extends Nesterov's $\pi/2$ bound from the cube $\{x_i^2 \le 1\}$ to systems of commuting quadratic constraints.
--
--   **Formalization Note** $f^*$ and $F^*$ enter through the predicates "is the least upper bound of the objective over the feasible set" (definition `ModernConvex.Relaxations.QuadraticSystem`); under the hypotheses both feasible sets are nonempty and bounded, so the values exist. The book's standing conditions of (SL.??) — symmetric $B_i$ and all $d_i \ge 0$ — are explicit hypotheses.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 314–315, Proposition 4.10.5, (4.10.137) (setting (SL.??), p. 313; (SDD), p. 314)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_QuadraticSystem

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Proposition 4.10.5 (Nesterov, Ye), pp. 314–315. Consider (SL.??) (p. 313):
symmetric `B₁, …, Bₘ`, all `dᵢ ≥ 0`, `f(x) = xᵀAx`, `f∗` the optimal value of (P) and `F∗` the
optimal value of (SDP). Assume
1. the matrices `B₁, …, Bₘ` commute with each other;
2. system (S′) is strictly feasible, and some combination of the `Bᵢ` with nonnegative
   coefficients is positive definite;
3. `A ⪰ 0`.
Then `f∗ ≥ 0`, (SDD) is solvable with the optimal value `F∗`, and `F∗ ≤ (π/2) f∗` (4.10.137). -/
theorem nesterov_ye {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hd : ∀ i, 0 ≤ S.d i)
    (hcomm : ∀ i j, S.B i * S.B j = S.B j * S.B i)
    (hstrict : S.StrictlyFeasible)
    (hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef)
    (hA : S.A.PosSemidef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧ Fstar ≤ Real.pi / 2 * fstar := by sorry

end ModernConvex.Relaxations
