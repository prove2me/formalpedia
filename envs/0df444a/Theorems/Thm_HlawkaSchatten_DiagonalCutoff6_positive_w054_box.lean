-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w054_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w054_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:55:41.306978+00:00
-- url     : https://prove2.me/theorems/72ffe3ba-44b6-4ecb-8f44-e47cb4342970
-- title:
--   Diagonal Hlawka coordinate box on [117/16, 59/8]
-- statement:
--   Let $p\in[117/16,59/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=143987/50000$, $A=18099/12500$, and $d=86049/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(9659/50000)M_i$ for $h\ne i$. Then
--   $$-75429/100000\le X_{ii}\le-58367/100000,\qquad 41109/50000\le X_{ji}\le 98917/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w054_box (p : ℝ) (hpa : (117/16 : ℝ) ≤ p) (hpb : p ≤ (59/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (143987/50000 : ℝ) (18099/12500 : ℝ) (86049/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9659/50000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(75429/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58367/100000 : ℝ) else (41109/50000 : ℝ) ≤ X j i ∧ X j i ≤ (98917/100000 : ℝ) := by sorry
