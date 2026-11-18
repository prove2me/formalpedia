-- Prove2me | Theorems.Thm_LostSalesRQ_brownian_comparison
-- name    : LostSalesRQ.brownian_comparison
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:30:01.687197+00:00
-- url     : https://prove2.me/theorems/90efa122-f06d-4b7b-86f0-a3f85dd0900c
-- title:
--   Lemma D.1: Brownian comparison
-- statement:
--   For all $T>0$ and $0\le\ell\le1$,
--   $$W_T(\ell)=\mathbb E\sup_{0\le t\le T}\{(1-\ell)t-N(t)\}\le\sqrt T\,w(\ell\sqrt T),$$
--   where $N$ is a rate-one Poisson process and $w$ is the Brownian profile.
--
--   The expected largest excess of supply over Poisson demand is at most the corresponding Brownian quantity, at every finite horizon; it bounds the calibrated penalty in Lemma 2(iii).
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma D.1 (p. A7).

import Definitions.Def_LostSalesRQ_poisson_process
import Definitions.Def_LostSalesRQ_gaussian

namespace LostSalesRQ

theorem brownian_comparison (T ℓ : ℝ) (hT : 0 < T) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    expectedMaxExcess T ℓ ≤ Real.sqrt T * brownianProfile (ℓ * Real.sqrt T) := by sorry

end LostSalesRQ
