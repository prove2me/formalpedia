-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_stability
-- name    : MinimaxInterventions1429.Separable.stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:02.476776+00:00
-- url     : https://prove2.me/theorems/bbbe8393-22eb-4314-b9c3-9381c67f2398
-- title:
--   Lemma 2.1 — stability
-- statement:
--   Let $m,k\ge2$, let $L\in[0,1]^{m\times k}$, and let $M,B$ be arbitrary real tables. Write $F_X(p)=\max_g\sum_hX_{gh}p_h$ on the closed simplex, and let $d_q$ denote distance modulo a common scalar. If $d_q(M,L)\le\tau$ and $p$ minimizes $F_{M+B}$, then
--
--   $$F_{L+B}(p)\le\min_{q\in\Delta_k}F_{L+B}(q)+2\tau.$$
--
--   The surcharge $B$ need not be separable or bounded. This stability statement relates a quotient-accurate table release to accurate decisions under every real intervention.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 2.1, printed p.9 (PDF p.11)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem stability {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L M B : Table m k) (hL : InCube L)
    (τ : ℝ) (hd : quotientDist M L ≤ τ) (p : Mixture k)
    (hp : Optimal (M + B) 0 p) : Optimal (L + B) (2 * τ) p := by sorry

end MinimaxInterventions1429.Separable
