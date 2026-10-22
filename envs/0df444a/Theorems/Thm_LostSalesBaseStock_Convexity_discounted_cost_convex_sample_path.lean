-- Prove2me | Theorems.Thm_LostSalesBaseStock_Convexity_discounted_cost_convex_sample_path
-- name    : LostSalesBaseStock.Convexity.discounted_cost_convex_sample_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:41:49.864669+00:00
-- url     : https://prove2.me/theorems/3c882db4-7236-428b-9c1a-374b1b02b60d
-- title:
--   Theorem 5 — with $h_2 = 0$ the discounted cost is convex in $S$ on every sample path
-- statement:
--   Consider a sample path of lead times $L(0), \dots, L(N)$ with noncrossing orders ($n + L(n)$ weakly increasing for $n \le N$, Assumption 1) and demands $D_0, \dots, D_N \ge 0$. Let $\pi_n(S)$ be the end-of-period inventory position and $l_n(S)$ the lost sales of the order-up-to-$S$ lost-sales system. For every discount factor $0 < \alpha \le 1$ and all cost parameters $h_1 \ge 0$, $p \ge 0$, the discounted cost with no storage cost,
--
--   $$
--   S \mapsto \sum_{n=0}^{N} \alpha^n \big( h_1 \, \pi_n(S) + p \, l_n(S) \big),
--   $$
--
--   is convex on $S \in [0, \infty)$.
--
--   This is the paper's first main result: when the only holding cost is charged on the inventory position, the discounted cost of a base-stock policy is convex in the base-stock level on every noncrossing sample path, and therefore also in expectation. The storage cost $h_2$ cannot be added on a sample path (the paper's Example 1 is a counterexample), and noncrossing cannot be dropped (Example 2).
--
--   **Formalization Note** The cost is the discounted cost (3.1) evaluated at $h_2 = 0$. The nonnegativity of $h_1$ and $p$ and the range $0 < \alpha \le 1$ are the paper's standing assumptions from Section 3.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 799, Theorem 5

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_arrivalIndex
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics
import Definitions.Def_LostSalesBaseStock_Convexity_discountedCost

namespace LostSalesBaseStock.Convexity

/-- Theorem 5 (Janakiraman–Roundy 2004, p. 799). On a sample path of lead times with
noncrossing orders (Assumption 1 on `{0, …, N}`) and nonnegative demands, for a discount
factor `0 < α ≤ 1` and nonnegative costs `h₁, p`, the discounted cost (3.1) with no storage
cost (`h₂ = 0`), `∑_{n=0}^{N} α^n (h₁ π_n(S) + p l_n(S))`, is convex in `S ∈ [0, ∞)`. -/
theorem discounted_cost_convex_sample_path (N : ℕ) (L : ℕ → ℕ)
    (hL : MonotoneOn (fun n => n + L n) (Set.Iic N))
    (D : ℕ → ℝ) (hD : ∀ n ≤ N, 0 ≤ D n)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1)
    (h₁ p : ℝ) (hh₁ : 0 ≤ h₁) (hp : 0 ≤ p) :
    ConvexOn ℝ (Set.Ici 0) (fun S : ℝ => discountedCost (arrivalIndex L) D N α h₁ 0 p S) := by sorry

end LostSalesBaseStock.Convexity
