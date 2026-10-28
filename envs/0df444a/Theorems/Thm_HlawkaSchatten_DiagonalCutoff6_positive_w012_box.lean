-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w012_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w012_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:38:39.296805+00:00
-- url     : https://prove2.me/theorems/7694cd02-cd3f-45a1-b11b-8f348b08e903
-- title:
--   Diagonal Hlawka coordinate box on [99/16, 397/64]
-- statement:
--   Let $p\in[99/16,397/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=238593/100000$, $A=75633/50000$, and $d=8373/10000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(8693/50000)M_i$ for $h\ne i$. Then
--   $$-69781/100000\le X_{ii}\le-1866/3125,\qquad 5207/6250\le X_{ji}\le 23411/25000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w012_box (p : ℝ) (hpa : (99/16 : ℝ) ≤ p) (hpb : p ≤ (397/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (238593/100000 : ℝ) (75633/50000 : ℝ) (8373/10000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8693/50000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69781/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1866/3125 : ℝ) else (5207/6250 : ℝ) ≤ X j i ∧ X j i ≤ (23411/25000 : ℝ) := by sorry
