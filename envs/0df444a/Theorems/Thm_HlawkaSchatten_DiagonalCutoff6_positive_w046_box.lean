-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w046_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w046_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:53:03.457383+00:00
-- url     : https://prove2.me/theorems/da62de75-23fb-467f-b3c5-491b78e7b0be
-- title:
--   Diagonal Hlawka coordinate box on [7, 225/32]
-- statement:
--   Let $p\in[7,225/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=274171/100000$, $A=146313/100000$, and $d=42737/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17837/100000)M_i$ for $h\ne i$. Then
--   $$-72689/100000\le X_{ii}\le-30067/50000,\qquad 41861/50000\le X_{ji}\le 9621/10000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w046_box (p : ℝ) (hpa : (7 : ℝ) ≤ p) (hpb : p ≤ (225/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (274171/100000 : ℝ) (146313/100000 : ℝ) (42737/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17837/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72689/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(30067/50000 : ℝ) else (41861/50000 : ℝ) ≤ X j i ∧ X j i ≤ (9621/10000 : ℝ) := by sorry
