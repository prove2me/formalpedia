-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w038_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w038_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:50:27.674828+00:00
-- url     : https://prove2.me/theorems/b947ba84-1a57-48da-b657-1e5b468832ed
-- title:
--   Symmetric Hlawka tail refinement 5 on [27/4, 217/32]
-- statement:
--   Let $p\in[27/4,217/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=263173/100000$, $A=147663/100000$, and $d=42489/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18177/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(18177/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w038_s4 (p : ℝ) (hpa : (27/4 : ℝ) ≤ p) (hpb : p ≤ (217/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (263173/100000 : ℝ) (147663/100000 : ℝ) (42489/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18177/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (18177/100000 : ℝ)*pair X i i := by sorry
