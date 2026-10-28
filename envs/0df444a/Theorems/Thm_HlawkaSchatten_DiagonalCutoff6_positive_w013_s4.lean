-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w013_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w013_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:40:36.003472+00:00
-- url     : https://prove2.me/theorems/2b4793cc-6c62-470a-9904-bc23c6e16086
-- title:
--   Symmetric Hlawka tail refinement 5 on [397/64, 199/32]
-- statement:
--   Let $p\in[397/64,199/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=29909/12500$, $A=9447/6250$, and $d=10471/12500$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17369/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(2171/12500)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w013_s4 (p : ℝ) (hpa : (397/64 : ℝ) ≤ p) (hpb : p ≤ (199/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29909/12500 : ℝ) (9447/6250 : ℝ) (10471/12500 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17369/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (2171/12500 : ℝ)*pair X i i := by sorry
