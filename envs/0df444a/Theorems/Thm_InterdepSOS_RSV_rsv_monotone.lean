-- Prove2me | Theorems.Thm_InterdepSOS_RSV_rsv_monotone
-- name    : InterdepSOS.RSV.rsv_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:33.48714+00:00
-- url     : https://prove2.me/theorems/44d7ff9c-9978-4971-9788-12f9dd04c76b
-- title:
--   §4, pp. 14–15 — the RS-V allocation is monotone for every partition
-- statement:
--   Fix a partition with candidate set $B$ and any allocation rule that, at every reported signal profile, selects a feasible subset of $B$ maximizing the sum of RS-V proxy weights $w_i=v_i(s_A,s_i,0_{B\setminus\{i\}})$. If values are weakly increasing in every signal and strictly increasing in each agent's own signal, then each agent's allocation is monotone in her own report:
--
--   $$
--   a\le b,\quad i\in x_B(a,s_{-i})\quad\Longrightarrow\quad i\in x_B(b,s_{-i}).
--   $$
--
--   This establishes the allocation property used to obtain ex-post IC-IR payments for every deterministic component of RS-V.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 14–15, proof of Theorem 4.1, opening monotonicity argument

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting

namespace InterdepSOS.RSV

theorem rsv_monotone {n : ℕ} (I : Set (Finset (Fin n)))
    (v : Valuation n) (hv : IsValuation v)
    (sel : Finset (Fin n) → Allocation n) (hsel : IsRSVSelector I v sel)
    (B : Finset (Fin n)) : IsMonotoneAlloc (sel B) := by sorry

end InterdepSOS.RSV
