-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w023_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w023_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:45:11.508039+00:00
-- url     : https://prove2.me/theorems/a18c4328-6248-4287-a6c9-e24c4899e43c
-- title:
--   Diagonal Hlawka coordinate box on [407/64, 51/8]
-- statement:
--   Let $p\in[407/64,51/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=246077/100000$, $A=150069/100000$, and $d=84133/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(859/5000)M_i$ for $h\ne i$. Then
--   $$-35011/50000\le X_{ii}\le-60219/100000,\qquad 8381/10000\le X_{ji}\le 93807/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w023_box (p : ℝ) (hpa : (407/64 : ℝ) ≤ p) (hpb : p ≤ (51/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (246077/100000 : ℝ) (150069/100000 : ℝ) (84133/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (859/5000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(35011/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(60219/100000 : ℝ) else (8381/10000 : ℝ) ≤ X j i ∧ X j i ≤ (93807/100000 : ℝ) := by sorry
