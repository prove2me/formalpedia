-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w014_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w014_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:41:35.169636+00:00
-- url     : https://prove2.me/theorems/0576a111-7f42-4562-a155-cfc06993b13d
-- title:
--   Diagonal Hlawka coordinate box on [199/32, 399/64]
-- statement:
--   Let $p\in[199/32,399/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=14997/6250$, $A=151041/100000$, and $d=16761/20000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(4337/25000)M_i$ for $h\ne i$. Then
--   $$-2182/3125\le X_{ii}\le-29903/50000,\qquad 41703/50000\le X_{ji}\le 46837/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w014_box (p : ℝ) (hpa : (199/32 : ℝ) ≤ p) (hpb : p ≤ (399/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14997/6250 : ℝ) (151041/100000 : ℝ) (16761/20000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4337/25000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(2182/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(29903/50000 : ℝ) else (41703/50000 : ℝ) ≤ X j i ∧ X j i ≤ (46837/50000 : ℝ) := by sorry
