-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w055_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w055_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:55:42.465976+00:00
-- url     : https://prove2.me/theorems/6c89769d-c77e-42cc-bb01-203509930048
-- title:
--   Diagonal Hlawka coordinate box on [59/8, 119/16]
-- statement:
--   Let $p\in[59/8,119/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=145371/50000$, $A=18063/12500$, and $d=43079/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(19221/100000)M_i$ for $h\ne i$. Then
--   $$-75489/100000\le X_{ii}\le-366/625,\qquad 82383/100000\le X_{ji}\le 2473/2500\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w055_box (p : ℝ) (hpa : (59/8 : ℝ) ≤ p) (hpb : p ≤ (119/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (145371/50000 : ℝ) (18063/12500 : ℝ) (43079/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19221/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(75489/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(366/625 : ℝ) else (82383/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2473/2500 : ℝ) := by sorry
