-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w053_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w053_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:55:28.762639+00:00
-- url     : https://prove2.me/theorems/dd5e91f3-df36-4d32-9d5f-243e78c17ee7
-- title:
--   Diagonal Hlawka coordinate box on [29/4, 117/16]
-- statement:
--   Let $p\in[29/4,117/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=285209/100000$, $A=145083/100000$, and $d=85937/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2427/12500)M_i$ for $h\ne i$. Then
--   $$-9421/12500\le X_{ii}\le-14543/25000,\qquad 20513/25000\le X_{ji}\le 49457/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w053_box (p : ℝ) (hpa : (29/4 : ℝ) ≤ p) (hpb : p ≤ (117/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (285209/100000 : ℝ) (145083/100000 : ℝ) (85937/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2427/12500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(9421/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(14543/25000 : ℝ) else (20513/25000 : ℝ) ≤ X j i ∧ X j i ≤ (49457/50000 : ℝ) := by sorry
