-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w013_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w013_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:39:55.12104+00:00
-- url     : https://prove2.me/theorems/f2118a82-1151-479a-bba2-0ab47977c976
-- title:
--   Diagonal Hlawka coordinate box on [397/64, 199/32]
-- statement:
--   Let $p\in[397/64,199/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=29909/12500$, $A=9447/6250$, and $d=10471/12500$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(2171/12500)M_i$ for $h\ne i$. Then
--   $$-17451/25000\le X_{ii}\le-59757/100000,\qquad 41679/50000\le X_{ji}\le 93661/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w013_box (p : ℝ) (hpa : (397/64 : ℝ) ≤ p) (hpb : p ≤ (199/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29909/12500 : ℝ) (9447/6250 : ℝ) (10471/12500 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2171/12500 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(17451/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59757/100000 : ℝ) else (41679/50000 : ℝ) ≤ X j i ∧ X j i ≤ (93661/100000 : ℝ) := by sorry
