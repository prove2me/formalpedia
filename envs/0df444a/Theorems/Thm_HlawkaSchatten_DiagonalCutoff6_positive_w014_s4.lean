-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w014_s4
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w014_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:41:41.058892+00:00
-- url     : https://prove2.me/theorems/24665328-3f47-4d03-a23d-76e8ef882612
-- title:
--   Symmetric Hlawka tail refinement 5 on [199/32, 399/64]
-- statement:
--   Let $p\in[199/32,399/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=14997/6250$, $A=151041/100000$, and $d=16761/20000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17349/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(4337/25000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w014_s4 (p : ℝ) (hpa : (199/32 : ℝ) ≤ p) (hpb : p ≤ (399/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14997/6250 : ℝ) (151041/100000 : ℝ) (16761/20000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17349/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (4337/25000 : ℝ)*pair X i i := by sorry
