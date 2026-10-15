-- Prove2me | Theorems.Thm_InterdepSOS_RSVCG_display_5
-- name    : InterdepSOS.RSVCG.display_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:20.742976+00:00
-- url     : https://prove2.me/theorems/002fe233-ab8d-44af-8035-26acd1d4c487
-- title:
--   Display (5), p. 17 — $\mathbb{E}_B[w_{iT}\cdot 1_{i\in B}] \ge v_{iT}(s_T)/2\cdot 1/2$
-- statement:
--   Consider separable SOS combinatorial valuations (Definitions 2.10 and 2.16) and a profile $s$ of true signals, reported truthfully. Partition the agents uniformly at random into $A$ and $B = [n] \setminus A$, and let $w_{iT} = v_{iT}(s_{iT}, s_{AT}, 0_{B-iT})$ be the RS-VCG proxy weight of agent $i$ for bundle $T$. Then for every agent $i$ and every bundle $T$,
--   $$\mathbb{E}_B\bigl[w_{iT} \cdot \mathbf 1_{i \in B}\bigr] \ge \frac{v_{iT}(s_T)}{2} \cdot \frac12,$$
--   where $\mathbb{E}_B$ is the average over all $2^n$ subsets $B \subseteq [n]$.
--
--   This is the step of the proof of Theorem 5.1 that obtains the factor 4: the paper derives it from Lemma 3.1 with $d = 1$ (a uniformly random half of the other signals zeroed keeps half of an SOS value in expectation), using that $i \in B$ with probability $1/2$.
--
--   **Formalization Note** The expectation is the finite average $2^{-n}\sum_{B \subseteq [n]}$ of $w_{iT}$ on the event $i \in B$ and $0$ otherwise.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 17, proof of Theorem 5.1, display (5)

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism

namespace InterdepSOS.RSVCG

theorem display_5 {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (s : Profile n m) (i : Fin n) (T : Bundle m) :
    v i T (sigT s T) / 2 * (1 / 2) ≤
      avgB (fun B => if i ∈ B then vcgWeight v B s i T else 0) := by sorry

end InterdepSOS.RSVCG
