-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w006_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w006_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:28:59.614994+00:00
-- url     : https://prove2.me/theorems/b5c053d9-4162-4a31-a04c-0b3bf2b9cd41
-- title:
--   Diagonal Hlawka coordinate box on [195/32, 391/64]
-- statement:
--   Let $p\in[195/32,391/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=234521/100000$, $A=75981/50000$, and $d=41751/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(8751/50000)M_i$ for $h\ne i$. Then
--   $$-34827/50000\le X_{ii}\le-59429/100000,\qquad 5189/6250\le X_{ji}\le 46777/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w006_box (p : ℝ) (hpa : (195/32 : ℝ) ≤ p) (hpb : p ≤ (391/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (234521/100000 : ℝ) (75981/50000 : ℝ) (41751/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8751/50000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(34827/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59429/100000 : ℝ) else (5189/6250 : ℝ) ≤ X j i ∧ X j i ≤ (46777/50000 : ℝ) := by sorry
