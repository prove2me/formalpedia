-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w017_s3
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w017_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:42:57.242657+00:00
-- url     : https://prove2.me/theorems/55bf2497-0094-4699-a438-9af7944664be
-- title:
--   Symmetric Hlawka tail refinement 4 on [401/64, 201/32]
-- statement:
--   Let $p\in[401/64,201/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=30249/12500$, $A=37677/25000$, and $d=20979/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17369/100000)M_i$ for $h\ne i$. Then
--   $$|(V_i)_h|\le(4323/25000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w017_s3 (p : ℝ) (hpa : (401/64 : ℝ) ≤ p) (hpb : p ≤ (201/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30249/12500 : ℝ) (37677/25000 : ℝ) (20979/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17369/100000 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (4323/25000 : ℝ)*pair X i i := by sorry
