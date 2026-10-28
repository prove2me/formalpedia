-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w047_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w047_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:53:28.636825+00:00
-- url     : https://prove2.me/theorems/73da4aa0-bdce-4a3a-b877-818077a695ed
-- title:
--   Diagonal Hlawka coordinate box on [225/32, 113/16]
-- statement:
--   Let $p\in[225/32,113/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=275549/100000$, $A=73077/50000$, and $d=85533/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3559/20000)M_i$ for $h\ne i$. Then
--   $$-9091/12500\le X_{ii}\le-30113/50000,\qquad 83801/100000\le X_{ji}\le 3007/3125\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w047_box (p : ℝ) (hpa : (225/32 : ℝ) ≤ p) (hpb : p ≤ (113/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (275549/100000 : ℝ) (73077/50000 : ℝ) (85533/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/20000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(9091/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(30113/50000 : ℝ) else (83801/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3007/3125 : ℝ) := by sorry
