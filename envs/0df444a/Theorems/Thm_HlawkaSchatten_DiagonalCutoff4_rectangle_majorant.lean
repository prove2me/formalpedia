-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
-- name    : HlawkaSchatten.DiagonalCutoff4.rectangle_majorant
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T10:17:35.011368+00:00
-- url     : https://prove2.me/theorems/2fcb9812-00f9-4dbf-a372-c0c11258f069
-- title:
--   Symmetric norm majorant on a positive tail interval
-- statement:
--   For $p\ge\max(1,a)$, three explicit power budgets at $(l,l),(h,l),(h,h)$ certify
--   $$\|(M,u,v)\|_p\le cM+\alpha(u+v)\quad(lM\le u,v\le hM),$$
--   where $M\ge0$, $0\le l<h\le1$, $\alpha\ge0$, and $c+2\alpha l\ge1$.
--   The budgets are $1+2l^a\le(c+2\alpha l)^a$, $1+h^a+l^a\le(c+\alpha(h+l))^a$, and $1+2h^a\le(c+2\alpha h)^a$.
--   This is a localization tool, not the cutoff-four theorem.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem HlawkaSchatten.DiagonalCutoff4.rectangle_majorant {p a lo hi c alpha M u v : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (hM : 0 ≤ M) (hlu : lo*M ≤ u) (huh : u ≤ hi*M)
    (hlv : lo*M ≤ v) (hvh : v ≤ hi*M) :
    (|M|^p+|u|^p+|v|^p)^(1/p) ≤ c*M+alpha*(u+v) := by sorry
