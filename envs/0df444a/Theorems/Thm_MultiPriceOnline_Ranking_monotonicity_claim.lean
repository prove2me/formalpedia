-- Prove2me | Theorems.Thm_MultiPriceOnline_Ranking_monotonicity_claim
-- name    : MultiPriceOnline.Ranking.monotonicity_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:26.685259+00:00
-- url     : https://prove2.me/theorems/18a4cb87-239d-4e71-ad85-d9295722ee74
-- title:
--   App. C, p. 46, Monotonicity claim in the proof of Lemma 3 — Zₜ ≥ Z^crit regardless of Wᵢ
-- statement:
--   In the setting of Algorithm 2 (deterministic case, booking limits from Proposition 1, an arbitrary maximizing tie-breaking rule), fix a customer $t$ and an item $i$, and seeds $W\in[0,1]^n$ under which no two distinct items share a strictly positive value of (23) at any customer. Let $Z_t$ be the pseudorevenue earned at time $t$ by the run of the algorithm with all items, and $Z^{\mathrm{crit}}$ the pseudorevenue earned at time $t$ by the run with item $i$ removed. Then
--   $$Z_t\ \ge\ Z^{\mathrm{crit}},$$
--   whatever the value of $W_i$.
--
--   With the Dominance claim, this gives $\mathbb E[Y_i+Z_t\mid W_{i'},\,i'\ne i]\ge r_i^{(j_{t,i})}$ in the proof of Lemma 3.
--
--   **Formalization Note** The no-ties hypothesis is the paper's "we ignore measure-zero events" (it fails on a null set of seeds). Without it the claim is false for some tie-breaking rules, which may remove different items in the two runs.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, App. C, p. 46, Monotonicity claim (2.) in the proof of Lemma 3

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

namespace MultiPriceOnline.Ranking

/-- Monotonicity claim (App. C, p. 46, proof of Lemma 3): the pseudorevenue `Z_t` earned at
customer `t` by the run with item `i` is at least `Z^crit`, the pseudorevenue earned at `t` by
the run with item `i` removed, whatever `W_i` is. Seeds in `[0, 1]ⁿ` without ties. -/
theorem monotonicity_claim {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (hr : ∀ i, IsPriceSet (m i) (r i)) (hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1) (hNT : NoTies m r α p W)
    (t : Fin T) (i : Fin n) :
    Zt m r α p sel (Finset.univ.erase i) W t ≤ Zt m r α p sel Finset.univ W t := by sorry

end MultiPriceOnline.Ranking
