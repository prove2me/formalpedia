-- Prove2me | Theorems.Thm_MultiPriceOnline_Ranking_dominance_claim
-- name    : MultiPriceOnline.Ranking.dominance_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:03.451674+00:00
-- url     : https://prove2.me/theorems/e7587c86-eb26-4023-895f-aebebf71c06d
-- title:
--   App. C, pp. 45–46, Dominance claim in the proof of Lemma 3 — if Wᵢ ∈ [0, W^crit) then item i gets matched
-- statement:
--   In the setting of Algorithm 2 (deterministic case, booking limits from Proposition 1, an arbitrary maximizing tie-breaking rule), fix a customer $t$ and an item $i$ with $j:=j_{t,i}\ge1$, and seeds $W\in[0,1]^n$ under which no two distinct items share a strictly positive value of (23) at any customer. Let $Z^{\mathrm{crit}}$ be the pseudorevenue earned at time $t$ by the run of the algorithm with item $i$ removed (it does not depend on $W_i$). Let $W^{\mathrm{crit}}\in[0,L_i^{(j)}]$ satisfy $\Phi_{\mathcal P_i}(W^{\mathrm{crit}})=\max\{r_i^{(j)}-Z^{\mathrm{crit}},0\}$.
--
--   **Dominance.** If $W_i\in[0,W^{\mathrm{crit}})$, then in the run with item $i$, item $i$ gets matched — to customer $t$ or to an earlier customer. Equivalently, since $\Phi_{\mathcal P_i}$ is a strictly increasing bijection from $[0,L_i^{(j)}]$ onto $[0,r_i^{(j)}]$ and $\Phi_{\mathcal P_i}(W_i)\ge0$,
--   $$\Phi_{\mathcal P_i}(W_i)\ <\ r_i^{(j)}-Z^{\mathrm{crit}}\quad\Longrightarrow\quad \text{item } i \text{ is assigned to some customer } s\le t.$$
--
--   Together with the Monotonicity claim, this is the core of Lemma 3: it lower-bounds $\mathbb E[Y_i\mid W_{i'},\,i'\ne i]$ by $\Phi_{\mathcal P_i}(W^{\mathrm{crit}})$.
--
--   **Formalization Note** The hypothesis is written as $\Phi_{\mathcal P_i}(W_i)<r_i^{(j)}-Z^{\mathrm{crit}}$ instead of $W_i<W^{\mathrm{crit}}$, which avoids defining $W^{\mathrm{crit}}$ by an inverse; the two are equivalent for $W_i\in[0,1]$ by the bijection stated above. The no-ties hypothesis is the paper's "we ignore measure-zero events": without it, a tie-breaking rule that resolves a tie differently in the two runs can make them diverge.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, App. C, pp. 45–46, Dominance claim (1.) in the proof of Lemma 3

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

namespace MultiPriceOnline.Ranking

/-- Dominance claim (App. C, pp. 45–46, proof of Lemma 3). Fix customer `t` and item `i` with
`j = j_{t,i} ≥ 1`, and let `Z^crit` be the pseudorevenue earned at `t` by the run with item `i`
removed. If `Φ_{𝒫_i}(W_i) < r_i^{(j)} - Z^crit` (equivalently `W_i ∈ [0, W^crit)`), then in the
run with item `i`, item `i` is matched at some customer `s ≤ t`. Seeds in `[0, 1]ⁿ` without
ties. -/
theorem dominance_claim {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, IsPriceSet (m i) (r i)) (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1) (hNT : NoTies m r α p W)
    (t : Fin T) (i : Fin n) (hj : 1 ≤ jt m (p t) i)
    (hcrit : Phi (m i) (r i) (α i) (W i) <
      MultiPriceOnline.Balance.pr (r i) (jt m (p t) i) - Zt m r α p sel (Finset.univ.erase i) W t) :
    ∃ s : Fin T, s ≤ t ∧ run2 m r α p sel Finset.univ W s = some i := by sorry

end MultiPriceOnline.Ranking
