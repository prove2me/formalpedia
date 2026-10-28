-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w003_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w003_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:07:06.618886+00:00
-- url     : https://prove2.me/theorems/2ea453ea-981b-4a30-8b1d-e292aefcf91b
-- title:
--   Symmetric Hlawka tail refinement 5 on [387/64, 97/16]
-- statement:
--   Let $p\in[387/64,97/16]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=232489/100000$, $A=76161/50000$, and $d=16677/20000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17559/100000)M_i$ for $h\ne i$. Then\n$$|(V_i)_h|\le(17557/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w003_s4 (p : ℝ) (hpa : (387/64 : ℝ) ≤ p) (hpb : p ≤ (97/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (232489/100000 : ℝ) (76161/50000 : ℝ) (16677/20000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17559/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (17557/100000 : ℝ)*pair X i i := by sorry
