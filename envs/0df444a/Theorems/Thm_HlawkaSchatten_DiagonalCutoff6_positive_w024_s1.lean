-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w024_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w024_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:45:44.730991+00:00
-- url     : https://prove2.me/theorems/b8563a99-2b22-4b77-84b7-02b4f3447ed0
-- title:
--   Symmetric Hlawka tail refinement 2 on [51/8, 409/64]
-- statement:
--   Let $p\in[51/8,409/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=246759/100000$, $A=37491/25000$, and $d=84169/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(51703/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(21979/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w024_s1 (p : ℝ) (hpa : (51/8 : ℝ) ≤ p) (hpb : p ≤ (409/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (246759/100000 : ℝ) (37491/25000 : ℝ) (84169/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (51703/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (21979/100000 : ℝ)*pair X i i := by sorry
