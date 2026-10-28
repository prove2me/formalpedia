-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w044_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w044_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:52:48.375139+00:00
-- url     : https://prove2.me/theorems/db91635b-ab13-414e-addb-6a457f828112
-- title:
--   Symmetric Hlawka tail refinement 5 on [111/16, 223/32]
-- statement:
--   Let $p\in[111/16,223/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=135709/50000$, $A=146637/100000$, and $d=85353/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(112/625)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(112/625)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w044_s4 (p : ℝ) (hpa : (111/16 : ℝ) ≤ p) (hpb : p ≤ (223/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (135709/50000 : ℝ) (146637/100000 : ℝ) (85353/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (112/625 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (112/625 : ℝ)*pair X i i := by sorry
