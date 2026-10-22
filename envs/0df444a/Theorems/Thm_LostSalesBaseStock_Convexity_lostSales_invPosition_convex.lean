-- Prove2me | Theorems.Thm_LostSalesBaseStock_Convexity_lostSales_invPosition_convex
-- name    : LostSalesBaseStock.Convexity.lostSales_invPosition_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:26:33.222429+00:00
-- url     : https://prove2.me/theorems/2e2ce900-c750-4fd7-b693-168f17afd4af
-- title:
--   Corollary 4 — discounted lost sales and inventory position are convex in $S$
-- statement:
--   Consider a sample path of lead times $L(0), \dots, L(N)$ with noncrossing orders ($n + L(n)$ weakly increasing for $n \le N$, Assumption 1) and demands $D_0, \dots, D_N \ge 0$. Let $l_n(S)$ be the lost sales and $\pi_n(S)$ the end-of-period inventory position of the order-up-to-$S$ lost-sales system. Then for every $m \in \{0, \dots, N\}$ and every nonnegative, weakly decreasing sequence $(\beta_n)$, both
--
--   $$
--   S \mapsto \sum_{n=0}^{m} \beta_n \, l_n(S) \qquad\text{and}\qquad S \mapsto \sum_{n=0}^{m} \beta_n \, \pi_n(S)
--   $$
--
--   are convex on $S \in [0, \infty)$.
--
--   With $\beta_n = \alpha^n$ these are the discounted lost sales and the discounted inventory position, the two cost components whose convexity gives the paper's first main result.
--
--   **Formalization Note** The two conclusions are stated as one conjunction. Assumption 1 is stated on $\{0, \dots, N\}$ only.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 798, Corollary 4

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_arrivalIndex
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics

namespace LostSalesBaseStock.Convexity

/-- Corollary 4 (Janakiraman–Roundy 2004, p. 798). On a sample path of lead times with
noncrossing orders (Assumption 1 on `{0, …, N}`) and nonnegative demands, for every
`m ∈ {0, …, N}` and every nonnegative, weakly decreasing sequence `β`, both
`∑_{n=0}^{m} β_n l_n(S)` and `∑_{n=0}^{m} β_n π_n(S)` are convex in `S ∈ [0, ∞)`. -/
theorem lostSales_invPosition_convex (N : ℕ) (L : ℕ → ℕ)
    (hL : MonotoneOn (fun n => n + L n) (Set.Iic N))
    (D : ℕ → ℝ) (hD : ∀ n ≤ N, 0 ≤ D n)
    (β : ℕ → ℝ) (hβ_nonneg : ∀ n, 0 ≤ β n) (hβ_anti : Antitone β)
    (m : ℕ) (hm : m ≤ N) :
    ConvexOn ℝ (Set.Ici 0)
        (fun S : ℝ => ∑ n ∈ Finset.range (m + 1), β n * lostSales (arrivalIndex L) D S n) ∧
      ConvexOn ℝ (Set.Ici 0)
        (fun S : ℝ =>
          ∑ n ∈ Finset.range (m + 1), β n * invPosition (arrivalIndex L) D S n) := by sorry

end LostSalesBaseStock.Convexity
