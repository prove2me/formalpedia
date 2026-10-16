-- Prove2me | Theorems.Thm_InterdepSOS_KHL_display_6_7
-- name    : InterdepSOS.KHL.display_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:43.786444+00:00
-- url     : https://prove2.me/theorems/65e783e7-da06-4e71-978e-31bdeb134129
-- title:
--   Displays (6)–(7), p. 19 — the welfare of any allocation is at most OTHER + SELF for SOS valuations on k signal values
-- statement:
--   Let $v$ be combinatorial valuations over the signal grid $\{0,\dots,k-1\}^n$ satisfying the standing assumptions (nonnegative, $v_{i\emptyset}\equiv0$, monotone, strictly increasing in the own signal on nonempty bundles), with every $v_{iT}$ SOS. Let $\mathbf s$ be a grid profile and $T=(T_1,\dots,T_n)$ any assignment of bundles. Then
--   $$\sum_i v_{iT_i}(\mathbf s)\;\le\;\sum_i v_{iT_i}(\mathbf s_{-i},0_i)+\sum_{i\,:\,s_i>0}\bigl(v_{iT_i}(\mathbf 0_{-i},s_i)-v_{iT_i}(\mathbf 0)\bigr)\qquad(6)$$
--   and
--   $$\sum_i v_{iT_i}(\mathbf s_{-i},0_i)+\sum_{i\,:\,s_i>0}\bigl(v_{iT_i}(\mathbf 0_{-i},s_i)-v_{iT_i}(\mathbf 0)\bigr)\;\le\;\underbrace{\sum_i v_{iT_i}(\mathbf s_{-i},0_i)}_{\mathsf{OTHER}}+\underbrace{\sum_{\ell=1}^{k-1}\sum_{i\,:\,s_i=\ell}v_{iT_i}(\mathbf 0_{-i},s_i)}_{\mathsf{SELF}}.\qquad(7)$$
--
--   This decomposition splits the welfare into the contribution of the other agents' signals and the contribution of each agent's own signal; the two terms are covered by Random Sampling (Lemma 6.3) and Random Threshold (Lemma 6.2).
--
--   **Formalization Note** The paper states the decomposition for a welfare-maximizing allocation $T^*$; its argument does not use optimality, and the statement here holds for every assignment of bundles (not even disjointness is required).
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 19, §6, displays (6)–(7)

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting

namespace InterdepSOS.KHL
theorem display_6_7 {n m : ℕ} (k : ℕ) (v : Valuation n m)
    (hv : IsCombValuation k v) (hsos : ∀ i T, IsSOS k (v i T))
    (s : Signal n) (hs : InGrid k s) (T : Allocation n m) :
    welfare v T s ≤ other v T s +
        ∑ i ∈ Finset.univ.filter (fun i => 0 < s i),
          (v i (T i) (Function.update (0 : Signal n) i (s i)) - v i (T i) (0 : Signal n)) ∧
      other v T s +
          ∑ i ∈ Finset.univ.filter (fun i => 0 < s i),
            (v i (T i) (Function.update (0 : Signal n) i (s i)) - v i (T i) (0 : Signal n)) ≤
        other v T s + self k v T s := by sorry
end InterdepSOS.KHL
