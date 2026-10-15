-- Prove2me | Theorems.Thm_InterdepSOS_RSV_lemma_3_1
-- name    : InterdepSOS.RSV.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:30.471493+00:00
-- url     : https://prove2.me/theorems/890c8730-a511-4a12-940a-47bb42a3fa85
-- title:
--   Lemma 3.1, p. 13 — random zeroing retains at least 1/(d+1) of a d-SOS value
-- statement:
--   Let $v_i$ be a nonnegative $d$-SOS valuation, with $d\ge0$. Keep agent $i$'s signal fixed, choose a subset $A$ of the other agents uniformly at random, and set all signals outside $A\cup\{i\}$ to zero. Then
--
--   $$
--   \mathbb E_A\bigl[v_i(s_A,0_B,s_i)\bigr]\ge \frac{v_i(s)}{d+1},\qquad B=([n]\setminus\{i\})\setminus A.
--   $$
--
--   This estimate relates proxy valuations obtained by random signal suppression to the original valuation and is reused in the paper's welfare bounds.
--
--   **Formalization Note** The printed lemma omits the range of $d$. The condition $d\ge0$ is necessary: a constant positive valuation satisfies the $d$-SOS increment condition for negative $d$, but violates the claimed bound when $-1<d<0$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 13, Lemma 3.1

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting

namespace InterdepSOS.RSV

theorem lemma_3_1 {n : ℕ} (w : Signal n → ℝ) (hw : ∀ s, 0 ≤ w s)
    (d : ℝ) (hd_nonneg : 0 ≤ d) (hd : IsDSOS d w) (i : Fin n)
    (s : Signal n) :
    1 / (d + 1) * w s ≤
      (2 ^ (n - 1) : ℝ)⁻¹ *
        ∑ A ∈ (Finset.univ.erase i).powerset, w (keepOn (insert i A) s) := by sorry

end InterdepSOS.RSV
