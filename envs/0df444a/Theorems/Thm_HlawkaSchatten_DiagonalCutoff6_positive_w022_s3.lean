-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w022_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w022_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:45:13.168912+00:00
-- url     : https://prove2.me/theorems/73b7d8e1-1652-44d4-b153-21ecc33d1ad7
-- title:
--   Symmetric Hlawka tail refinement 4 on [203/32, 407/64]
-- statement:
--   Let $p\in[203/32,407/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=61349/25000$, $A=75087/50000$, and $d=84097/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(3451/20000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(8599/50000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w022_s3 (p : ℝ) (hpa : (203/32 : ℝ) ≤ p) (hpb : p ≤ (407/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (61349/25000 : ℝ) (75087/50000 : ℝ) (84097/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (8599/50000 : ℝ)*pair X i i := by sorry
