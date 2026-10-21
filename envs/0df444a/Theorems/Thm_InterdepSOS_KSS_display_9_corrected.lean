-- Prove2me | Theorems.Thm_InterdepSOS_KSS_display_9_corrected
-- name    : InterdepSOS.KSS.display_9_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:45.411004+00:00
-- url     : https://prove2.me/theorems/a9e01ddd-1fb1-49da-b7d3-c54fe5b17031
-- title:
--   Display (9), p. 22, corrected — SELF is at most twice the bucketed sum of v_{iT_i}(0_{−i}, 2^{ℓ−1}) under strong-SOS
-- statement:
--   Let $k=2^q$ and let $v$ be a combinatorial valuation on $\{0,\dots,k-1\}^n$ that is strong-SOS for every agent and bundle. Then for every grid profile $\mathbf s$ and every allocation $T$,
--   $$\mathsf{SELF}=\sum_{\ell=1}^{k-1}\sum_{i\,:\,s_i=\ell}v_{iT_i}(\mathbf 0_{-i},s_i)\;\le\;2\sum_{\ell=1}^{\log_2 k}\;\sum_{i\,:\,2^{\ell-1}\le s_i<2^{\ell}}v_{iT_i}(\mathbf 0_{-i},2^{\ell-1}_i).$$
--
--   The signals $1,\dots,k-1$ split into the buckets $[2^{\ell-1},2^\ell)$, and within each bucket the contribution of an agent's own signal is compared with its value at the bucket floor. This is the bound that Random Bucket approximates (Lemma 6.4).
--
--   **Formalization Note** The paper's display (9) states this inequality **without the factor 2**, and as printed it is false: one agent, one item, $v(\mathbf s)=s_1$ (strong-SOS and strictly increasing), $k=4$, $s_1=3$ give $\mathsf{SELF}=3$ and right side $2$. The statement here carries the factor 2; it is the $d=1$ case of the paper's own display (12) (Appendix C, p. 33, factor $d(d+1)$), and Lemma 6.4's ratio $2\log_2 k$ needs exactly this factor. The milestone quotes (9) as printed. The bound holds for every allocation $T$; neither feasibility nor optimality of $T^*$ is used. $k=2^q$ with $\log_2 k=q$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 22, display (9) (corrected by the factor 2 of display (12), p. 33, at d = 1)

import Mathlib
import Definitions.Def_InterdepSOS_KSS_Setting

namespace InterdepSOS.KSS
theorem display_9_corrected {n m : ℕ} (q : ℕ) (v : InterdepSOS.KHL.Valuation n m)
    (hv : InterdepSOS.KHL.IsCombValuation (2 ^ q) v) (hss : ∀ i T, IsStrongSOS (2 ^ q) (v i T))
    (s : InterdepSOS.KHL.Signal n) (hs : InterdepSOS.KHL.InGrid (2 ^ q) s) (T : InterdepSOS.KHL.Allocation n m) :
    InterdepSOS.KHL.self (2 ^ q) v T s ≤
      2 * ∑ ℓ ∈ Finset.Icc 1 q,
        ∑ i ∈ Finset.univ.filter (fun i => 2 ^ (ℓ - 1) ≤ s i ∧ s i < 2 ^ ℓ),
          v i (T i) (Function.update (0 : InterdepSOS.KHL.Signal n) i (2 ^ (ℓ - 1))) := by sorry
end InterdepSOS.KSS
