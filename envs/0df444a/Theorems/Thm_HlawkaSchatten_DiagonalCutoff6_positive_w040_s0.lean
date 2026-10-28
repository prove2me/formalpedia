-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w040_s0
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w040_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:51:06.183214+00:00
-- url     : https://prove2.me/theorems/e596d693-be95-49e4-9cb7-d25889b73a8a
-- title:
--   Symmetric Hlawka tail refinement 1 on [109/16, 219/32]
-- statement:
--   Let $p\in[109/16,219/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=265919/100000$, $A=9207/6250$, and $d=17021/20000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(48009/100000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w040_s0 (p : ℝ) (hpa : (109/16 : ℝ) ≤ p) (hpb : p ≤ (219/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (265919/100000 : ℝ) (9207/6250 : ℝ) (17021/20000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (48009/100000 : ℝ)*pair X i i := by sorry
