-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w041_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w041_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:51:38.235132+00:00
-- url     : https://prove2.me/theorems/f620117e-fb01-4823-8e3d-760e074590cc
-- title:
--   Diagonal Hlawka coordinate box on [219/32, 55/8]
-- statement:
--   Let $p\in[219/32,55/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=66823/25000$, $A=147141/100000$, and $d=5323/6250$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18049/100000)M_i$ for $h\ne i$. Then
--   $$-4531/6250\le X_{ii}\le-7459/12500,\qquad 20829/25000\le X_{ji}\le 19227/20000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w041_box (p : ℝ) (hpa : (219/32 : ℝ) ≤ p) (hpb : p ≤ (55/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (66823/25000 : ℝ) (147141/100000 : ℝ) (5323/6250 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18049/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(4531/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(7459/12500 : ℝ) else (20829/25000 : ℝ) ≤ X j i ∧ X j i ≤ (19227/20000 : ℝ) := by sorry
