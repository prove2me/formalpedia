-- Prove2me | Theorems.Thm_InterdepSOS_RSVCG_expost_ic
-- name    : InterdepSOS.RSVCG.expost_ic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:20.212648+00:00
-- url     : https://prove2.me/theorems/ba9afc31-0611-49f8-b7dc-8e7935df334e
-- title:
--   §5, proof of Theorem 5.1, p. 18 — for every partition, RS-VCG is ex-post incentive compatible
-- statement:
--   Consider separable SOS combinatorial valuations and the Random-Sampling VCG mechanism with an arbitrary maximising allocation selector. Fix the partition $(A, B)$. Then the deterministic mechanism with allocation $\tilde s \mapsto \{T_i(\tilde s)\}$ and payments $p_i(\tilde s)$ is **ex-post incentive compatible**: for every agent $i$, every true profile $s$ and every report $s'_i$ of agent $i$ (one signal per bundle),
--   $$v_{iT'_i}(s_{T'_i}) - p_i(s'_i, s_{-i}) \le v_{iT^*_i}(s_{T^*_i}) - p_i(s),$$
--   where $T'_i$ and $T^*_i$ are the bundles allocated to $i$ at $(s'_i, s_{-i})$ and at $s$.
--
--   Since this holds for every partition, RS-VCG is universally ex-post IC.
--
--   **Formalization Note** The selector may break ties arbitrarily; the inequality is claimed for every maximising selector. Losers pay $0$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 17–18, proof of Theorem 5.1, IC display

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism

namespace InterdepSOS.RSVCG

theorem expost_ic {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) :
    IsExPostIC v (alloc B) (vcgPay v g alloc B) := by sorry

end InterdepSOS.RSVCG
