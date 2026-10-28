-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
-- name    : HlawkaSchatten.DiagonalCutoff6.signed_majorant
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T18:39:15.075406+00:00
-- url     : https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a
-- title:
--   Affine bound on two signed tails of a dominant coordinate
-- statement:
--   Let $p\ge a>0$ with $p\ge1$, $0<\rho\le1$, and $\alpha\ge0$. Suppose $1+\rho^a\le(1+\alpha\rho)^a$ and $1+2\rho^a\le(1+2\alpha\rho)^a$. For $M\ge0$ and $|u|,|v|\le\rho M$,\n$$\bigl(M^p+|u|^p+|v|^p\bigr)^{1/p}\le M+\alpha(|u|+|v|).$$\nThis affine bound retains the tail coordinates in the cutoff-6 localization.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem HlawkaSchatten.DiagonalCutoff6.signed_majorant {p a rho alpha M u v : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (hM : 0 ≤ M) (hu : |u| ≤ rho*M) (hv : |v| ≤ rho*M) :
    (|M|^p+|u|^p+|v|^p)^(1/p) ≤ M+alpha*(|u|+|v|) := by sorry
