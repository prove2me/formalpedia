-- Prove2me | Theorems.Thm_InterdepSOS_RSVCG_expost_ir
-- name    : InterdepSOS.RSVCG.expost_ir
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:19.318299+00:00
-- url     : https://prove2.me/theorems/80c79120-8b6e-4ae6-94f4-f885fa0634a1
-- title:
--   §5, proof of Theorem 5.1, p. 18 — for every partition, RS-VCG is ex-post individually rational
-- statement:
--   Consider separable SOS combinatorial valuations and the Random-Sampling VCG mechanism with an arbitrary maximising allocation selector. Fix the partition $(A, B)$. Then the deterministic mechanism is **ex-post individually rational**: for every agent $i$ and every true profile $s$, reported truthfully,
--   $$v_{iT^*_i}(s_{T^*_i}) - p_i(s) \ge 0,$$
--   where $T^*_i$ is the bundle allocated to $i$ at $s$.
--
--   Since this holds for every partition, RS-VCG is universally ex-post IR.
--
--   **Formalization Note** Losers pay $0$, so their utility is $0$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 18, proof of Theorem 5.1, IR display

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism

namespace InterdepSOS.RSVCG

theorem expost_ir {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) :
    IsExPostIR v (alloc B) (vcgPay v g alloc B) := by sorry

end InterdepSOS.RSVCG
