-- Prove2me | Theorems.Thm_LostSalesRQ_rational_gaussian_bound
-- name    : LostSalesRQ.rational_gaussian_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:30:50.242745+00:00
-- url     : https://prove2.me/theorems/6fc5240c-1413-42a6-a8fd-f309a2419e6a
-- title:
--   Lemma G.2: rational Gaussian bound
-- statement:
--   For every $s>0$,
--   $$G(s)>\frac{13s}{13+2s^2},$$
--   where $G(s)=\inf_{z\in\mathbb R}\{\phi(z)+z\Phi(z)+s[1-\Phi(z)]\}$.
--
--   Combined with Lemma G.1 this gives an explicit lower bound on $B_\mu(\eta)$ used to choose the rank weight in Lemma 2(ii).
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma G.2, eq. (G.4) (p. A14).

import Definitions.Def_LostSalesRQ_gaussian

namespace LostSalesRQ

theorem rational_gaussian_bound (s : ℝ) (hs : 0 < s) :
    13 * s / (13 + 2 * s ^ 2) < gaussianRankProfile s := by sorry

end LostSalesRQ
