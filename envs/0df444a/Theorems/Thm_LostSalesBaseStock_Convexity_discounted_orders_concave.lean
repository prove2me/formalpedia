-- Prove2me | Theorems.Thm_LostSalesBaseStock_Convexity_discounted_orders_concave
-- name    : LostSalesBaseStock.Convexity.discounted_orders_concave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:13:03.264723+00:00
-- url     : https://prove2.me/theorems/3b82bbd1-8f74-4190-bab2-6feb10a6ca75
-- title:
--   Lemma 3 — the weighted sum of orders $\sum_{n=0}^m \beta_n q_n(S)$ is concave in $S$
-- statement:
--   Consider a sample path of lead times $L(0), \dots, L(N)$ and demands $D_0, \dots, D_N \ge 0$, and assume that orders do not cross: $n + L(n)$ is weakly increasing for $n \in \{0, \dots, N\}$ (Assumption 1). Let $\lambda_n$ be the arrival index of $L$ and let $q_n(S)$ be the orders of the order-up-to-$S$ lost-sales system. Then for every $m \in \{0, \dots, N+1\}$ and every nonnegative, weakly decreasing sequence $(\beta_n)$, the function
--
--   $$
--   W_m^{\{\beta_n\}}(S) = \sum_{n=0}^{m} \beta_n \, q_n(S) = \sum_{n=1}^{m} \beta_n \, y_{n-1}(S)
--   $$
--
--   is concave in the base-stock level $S \in [0, \infty)$.
--
--   Individual orders $q_n(S)$ are neither convex nor concave in $S$; the lemma says that a discounted sum of them is concave. It is the basic sample-path fact behind both main results of the paper.
--
--   **Formalization Note** Assumption 1 is stated on $\{0, \dots, N\}$ only (`MonotoneOn` on `Set.Iic N`), because the dynamics up to $q_{N+1}$ depend on $L(0), \dots, L(N)$ only. The weights $\beta$ form a sequence indexed by $\mathbb{N}$; the domain of $S$ is $[0, \infty)$.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 798, Lemma 3

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_arrivalIndex
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics

namespace LostSalesBaseStock.Convexity

/-- Lemma 3 (Janakiraman–Roundy 2004, p. 798). On a sample path of lead times `L(0), …, L(N)`
with noncrossing orders (Assumption 1: `n + L(n)` weakly increasing for `n ≤ N`) and
nonnegative demands `D_0, …, D_N`, for every `m ∈ {0, …, N + 1}` and every nonnegative, weakly
decreasing sequence `β`, the weighted sum of orders `W_m(S) = ∑_{n=0}^{m} β_n q_n(S)` is concave
in the base-stock level `S ∈ [0, ∞)`. -/
theorem discounted_orders_concave (N : ℕ) (L : ℕ → ℕ)
    (hL : MonotoneOn (fun n => n + L n) (Set.Iic N))
    (D : ℕ → ℝ) (hD : ∀ n ≤ N, 0 ≤ D n)
    (β : ℕ → ℝ) (hβ_nonneg : ∀ n, 0 ≤ β n) (hβ_anti : Antitone β)
    (m : ℕ) (hm : m ≤ N + 1) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun S : ℝ => ∑ n ∈ Finset.range (m + 1), β n * orderQty (arrivalIndex L) D S n) := by sorry

end LostSalesBaseStock.Convexity
