-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w002_s2
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w002_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:06:55.108414+00:00
-- url     : https://prove2.me/theorems/d13bca04-cdf5-4e8e-b8e0-82583d858245
-- title:
--   Symmetric Hlawka tail refinement 3 on [193/32, 387/64]
-- statement:
--   Let $p\in[193/32,387/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=231811/100000$, $A=30489/20000$, and $d=41673/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(6313/25000)M_i$ for $h\ne i$. Then\n$$|(V_i)_h|\le(711/4000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w002_s2 (p : ℝ) (hpa : (193/32 : ℝ) ≤ p) (hpb : p ≤ (387/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (231811/100000 : ℝ) (30489/20000 : ℝ) (41673/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6313/25000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (711/4000 : ℝ)*pair X i i := by sorry
