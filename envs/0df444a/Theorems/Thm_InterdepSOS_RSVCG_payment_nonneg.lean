-- Prove2me | Theorems.Thm_InterdepSOS_RSVCG_payment_nonneg
-- name    : InterdepSOS.RSVCG.payment_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:19.349418+00:00
-- url     : https://prove2.me/theorems/b7d9958d-0def-4955-8920-492fe046d975
-- title:
--   §5, p. 17 — the RS-VCG payments are always nonnegative
-- statement:
--   Consider separable SOS combinatorial valuations and the Random-Sampling VCG mechanism with an arbitrary maximising allocation selector. Then for every partition $(A, B)$, every reported profile $\tilde s$ and every agent $i$,
--   $$p_i(\tilde s) \ge 0.$$
--
--   For a winner $i \in B$ with bundle $T_i$ this follows, in the paper, from $w_{-i} \ge \sum_{j \in B\setminus\{i\}} w_{jT_j}$ and from $g_{-iT_i}(\tilde s_{-iT_i}) \ge g_{-iT_i}(\tilde s_{AT_i}, 0_{B-iT_i})$; every other agent pays $0$.
--
--   **Formalization Note** Agents of $A$ and agents of $B$ allocated the empty bundle pay $0$ by definition.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 17, §5, paragraph before Theorem 5.1

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism

namespace InterdepSOS.RSVCG

theorem payment_nonneg {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (B : Finset (Fin n)) (s : Profile n m) (i : Fin n) :
    0 ≤ vcgPay v g alloc B s i := by sorry

end InterdepSOS.RSVCG
