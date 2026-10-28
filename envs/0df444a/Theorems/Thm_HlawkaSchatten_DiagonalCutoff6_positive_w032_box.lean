-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w032_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w032_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:48:10.055312+00:00
-- url     : https://prove2.me/theorems/8e21eaf6-42ec-489c-9954-c07c6753e010
-- title:
--   Diagonal Hlawka coordinate box on [105/16, 211/32]
-- statement:
--   Let $p\in[105/16,211/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=254953/100000$, $A=148767/100000$, and $d=10573/12500$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(461/2500)M_i$ for $h\ne i$. Then
--   $$-72153/100000\le X_{ii}\le-58817/100000,\qquad 82531/100000\le X_{ji}\le 9599/10000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w032_box (p : ℝ) (hpa : (105/16 : ℝ) ≤ p) (hpb : p ≤ (211/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (254953/100000 : ℝ) (148767/100000 : ℝ) (10573/12500 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/2500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72153/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58817/100000 : ℝ) else (82531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (9599/10000 : ℝ) := by sorry
