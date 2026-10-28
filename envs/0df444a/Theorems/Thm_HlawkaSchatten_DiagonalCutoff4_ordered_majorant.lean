-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
-- name    : HlawkaSchatten.DiagonalCutoff4.ordered_majorant
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T00:27:33.80714+00:00
-- url     : https://prove2.me/theorems/52674cf0-8e56-433b-afef-d29182021267
-- title:
--   Ordered three-coordinate norm bound from three vertices
-- statement:
--   Let $p\ge\max\{1,a\}$, $a>0$, $0<\rho\le1$, and $\alpha,\beta\ge0$ satisfy
--   $$1+\rho^a\le(1+\alpha\rho)^a,\qquad 1+2\rho^a\le(1+(\alpha+\beta)\rho)^a.$$
--   For $M\ge0$ and $|v|\le|u|\le\rho M$,
--   $$\bigl(|M|^p+|u|^p+|v|^p\bigr)^{1/p}\le M+\alpha|u|+\beta|v|.$$
--   This is an analytic tool for the proposed cutoff-four extension, not the full cutoff theorem.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem HlawkaSchatten.DiagonalCutoff4.ordered_majorant {p a rho alpha beta M u v : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (hM : 0 ≤ M) (hvu : |v| ≤ |u|) (hu : |u| ≤ rho*M) :
    (|M|^p+|u|^p+|v|^p)^(1/p) ≤ M+alpha*|u|+beta*|v| := by sorry
