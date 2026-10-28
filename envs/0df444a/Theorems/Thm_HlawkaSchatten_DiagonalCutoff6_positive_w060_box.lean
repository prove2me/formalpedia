-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w060_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w060_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:57:39.307057+00:00
-- url     : https://prove2.me/theorems/f1f7c10f-4980-4f7d-b3b6-63ba6278245e
-- title:
--   Diagonal Hlawka coordinate box on [123/16, 31/4]
-- statement:
--   Let $p\in[123/16,31/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=304611/100000$, $A=3579/2500$, and $d=43341/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3751/20000)M_i$ for $h\ne i$. Then
--   $$-37899/50000\le X_{ii}\le-29749/50000,\qquad 20789/25000\le X_{ji}\le 49469/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w060_box (p : ℝ) (hpa : (123/16 : ℝ) ≤ p) (hpb : p ≤ (31/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (304611/100000 : ℝ) (3579/2500 : ℝ) (43341/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3751/20000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(37899/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29749/50000 : ℝ) else (20789/25000 : ℝ) ≤ X j i ∧ X j i ≤ (49469/50000 : ℝ) := by sorry
