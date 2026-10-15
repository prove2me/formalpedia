-- Prove2me | Theorems.Thm_InterdepSOS_RSV_proposition_2_1
-- name    : InterdepSOS.RSV.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:31.225085+00:00
-- url     : https://prove2.me/theorems/250e6226-9333-4e00-816d-7a9194b29bec
-- title:
--   Proposition 2.1, p. 10 — ex-post IC-IR payments exist exactly for monotone allocations
-- statement:
--   Let each agent's value of service be nonnegative, weakly increasing in all signals, and strictly increasing in her own signal. For any deterministic served-set rule $x$, a payment rule depending only on reported signals makes $(x,p)$ ex-post incentive compatible and individually rational if and only if each agent's chance of being served is monotone in her own reported signal:
--
--   $$
--   (\exists p:\;\mathrm{IC}(x,p)\land\mathrm{IR}(x,p))\quad\Longleftrightarrow\quad \forall i,s_{-i},a\le b,\; i\in x(a,s_{-i})\implies i\in x(b,s_{-i}).
--   $$
--
--   This characterization turns a monotonicity result for a deterministic allocation into an existence result for truthful and individually rational payments.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 10, Proposition 2.1

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting

namespace InterdepSOS.RSV

theorem proposition_2_1 {n : ℕ} (v : Valuation n) (hv : IsValuation v)
    (x : Allocation n) :
    (∃ p : Payment n, IsExPostIC v x p ∧ IsExPostIR v x p) ↔
      IsMonotoneAlloc x := by sorry

end InterdepSOS.RSV
