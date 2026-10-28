-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w016_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w016_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:42:25.200531+00:00
-- url     : https://prove2.me/theorems/cfbbde78-56bb-443c-ac2a-0fa08cf930da
-- title:
--   Diagonal Hlawka coordinate box on [25/4, 401/64]
-- statement:
--   Let $p\in[25/4,401/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=7541/3125$, $A=150819/100000$, and $d=83879/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17309/100000)M_i$ for $h\ne i$. Then
--   $$-34933/50000\le X_{ii}\le-59899/100000,\qquad 41749/50000\le X_{ji}\le 93703/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w016_box (p : ℝ) (hpa : (25/4 : ℝ) ≤ p) (hpb : p ≤ (401/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7541/3125 : ℝ) (150819/100000 : ℝ) (83879/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17309/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(34933/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59899/100000 : ℝ) else (41749/50000 : ℝ) ≤ X j i ∧ X j i ≤ (93703/100000 : ℝ) := by sorry
