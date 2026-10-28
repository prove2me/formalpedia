-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_normalized_frame_failure
-- name    : HlawkaSchatten.DiagonalCutoff6.normalized_frame_failure
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:11:58.640318+00:00
-- url     : https://prove2.me/theorems/b5c4bafd-cdf1-4999-ad8b-297b5c19a98e
-- title:
--   Normalize a Hlawka counterexample with distinct maximal pair coordinates
-- statement:
--   Let $p>1$, $0<q<1$, $1\le k<K_p$, and $0<d\le1$. Suppose the scalar envelope satisfies $E_p(q)<K_p$, $d3^{1/p}\le1$, and $0\le k(2-d)-d$ with $[k(2-d)-d]3q<3d(k-1)$. Every strict real-three-dimensional counterexample then has a normalized counterpart satisfying the signed localization constraints, with each complementary pair attaining its positive maximum at its assigned coordinate.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.normalized_frame_failure {p q k d : ℝ} (hp : 1 < p)
    (hq0 : 0 < q) (hq1 : q < 1) (hk : 1 ≤ k)
    (hd : 0 < d) (hd1 : d ≤ 1) (hdroot : d*(3 : ℝ)^(1/p) ≤ 1)
    (hslope : 0 ≤ k*(2-d)-d)
    (hmargin : (k*(2-d)-d)*(3*q) < 3*d*(k-1))
    (hlinear : k < cyclicConstant p) (henvelope : scalarEnvelope p q < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ, Frame p k (3*q) d X ∧ tripleDeficit p (cyclicConstant p) X < 0 := by sorry
