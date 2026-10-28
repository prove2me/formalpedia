-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w001_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w001_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:07:00.354612+00:00
-- url     : https://prove2.me/theorems/6ac2d671-6817-4d14-ae1b-717cdddbebd1
-- title:
--   Diagonal Hlawka coordinate box on [385/64, 193/32]
-- statement:
--   Let $p\in[385/64,193/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=46227/20000$, $A=30513/20000$, and $d=41653/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(4399/25000)M_i$ for $h\ne i$. Then\n$$-69547/100000\le X_{ii}\le-11839/20000,\qquad 4139/5000\le X_{ji}\le 93473/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w001_box (p : ℝ) (hpa : (385/64 : ℝ) ≤ p) (hpb : p ≤ (193/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46227/20000 : ℝ) (30513/20000 : ℝ) (41653/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4399/25000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69547/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11839/20000 : ℝ) else (4139/5000 : ℝ) ≤ X j i ∧ X j i ≤ (93473/100000 : ℝ) := by sorry
