-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w004_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w004_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:18:59.441432+00:00
-- url     : https://prove2.me/theorems/dc782d74-43c6-4eef-a3b7-d4b633a0fa01
-- title:
--   Symmetric Hlawka tail refinement 5 on [97/16, 389/64]
-- statement:
--   Let $p\in[97/16,389/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=116583/50000$, $A=76101/50000$, and $d=2607/3125$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17541/100000)M_i$ for $h\ne i$. Then\n$$|(V_i)_h|\le(17539/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w004_s4 (p : ℝ) (hpa : (97/16 : ℝ) ≤ p) (hpb : p ≤ (389/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (116583/50000 : ℝ) (76101/50000 : ℝ) (2607/3125 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17541/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (17539/100000 : ℝ)*pair X i i := by sorry
