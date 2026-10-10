-- Prove2me | Theorems.Thm_MultiPriceOnline_Ranking_theorem_2
-- name    : MultiPriceOnline.Ranking.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:57.069506+00:00
-- url     : https://prove2.me/theorems/4436b477-6a61-4367-8aa3-38edd06bf35c
-- title:
--   Theorem 2, p. 16 — in the deterministic case, Multi-price Ranking is minᵢ F(𝒫ᵢ)-competitive
-- statement:
--   A firm sells $n\ge1$ items, one unit each ($k_i=1$). Item $i$ has a price set $\mathcal P_i=\{r_i^{(1)}<\dots<r_i^{(m_i)}\}$ with $r_i^{(1)}>0$, booking limits $\alpha_i^{(1)},\dots,\alpha_i^{(m_i)}$ (Proposition 1) and $F(\mathcal P_i)=1-e^{-\alpha_i^{(1)}}$. Customers $t=1,\dots,T$ arrive in the deterministic case: every purchase probability $p^{(j)}_{t,i}$ is $0$ or $1$. Multi-price Ranking draws independent uniform seeds $W_i\in[0,1]$ and offers each customer an available item maximizing $r_i^{(j_{t,i})}-\Phi_{\mathcal P_i}(W_i)$ at price $j_{t,i}$, when that maximum is positive, ties broken by any rule that returns a maximizer. Then for every arrival sequence and every feasible solution $x$ of the LP (5),
--   $$\min_{i\in[n]}F(\mathcal P_i)\cdot\sum_{t,i,j}p^{(j)}_{t,i}\,r_i^{(j)}\,x^{(j)}_{t,i}\ \le\ \mathbb E\bigl[\mathrm{ALG}(\mathcal S,\mathcal A)\bigr].$$
--   Equivalently, $\mathbb E[\mathrm{ALG}(\mathcal S,\mathcal A)]\ge\min_iF(\mathcal P_i)\cdot\mathrm{OPT}(\mathcal S,\mathcal A)$: Multi-price Ranking achieves a competitive ratio of $\min_iF(\mathcal P_i)$.
--
--   The ratio depends on the price sets only. Theorem 3 of the paper shows that, for setups in which every item has the same price set $\mathcal P$, no online algorithm can guarantee more than $F(\mathcal P)$.
--
--   **Formalization Note** The competitive ratio (6) is stated multiplied out, for every feasible $x$ of (5), so that $\mathrm{OPT}=0$ causes no division and no supremum is needed. The paper assumes $k_i=1$ "without loss of generality" for Algorithm 2; the statement is for setups with $k_i=1$, and an item with $k_i$ units corresponds to $k_i$ unit items with the same price set. $n\ge1$ is assumed so that the minimum exists; with no items both sides are $0$. The expectation is the integral over $[0,1]^n$ with the product of uniform laws.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 16, Theorem 2 (Algorithm 2, p. 22; proof p. 23)

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

namespace MultiPriceOnline.Ranking

open MeasureTheory

/-- Theorem 2 (p. 16): for any setup in the deterministic case (with every `k_i = 1`),
Multi-price Ranking achieves a competitive ratio of `min_i F(𝒫_i)`: for every arrival sequence,
every tie-breaking rule and every feasible solution `x` of the LP (5),
`min_i F(𝒫_i) · obj(x) ≤ E[ALG]`, the expectation over the seeds `W_i` i.i.d. uniform on
`[0, 1]`. -/
theorem theorem_2 {n T : ℕ} (hn : 0 < n) (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, IsPriceSet (m i) (r i)) (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (x : Fin T → Fin n → ℕ → ℝ) (hx : LPFeasible (fun _ => 1) m p x) :
    (Finset.univ.inf' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i => F (α i)) * lpObj m r p x ≤
      ∫ W, rev2 m r α p sel Finset.univ W ∂(seedMeasure n) := by sorry

end MultiPriceOnline.Ranking
