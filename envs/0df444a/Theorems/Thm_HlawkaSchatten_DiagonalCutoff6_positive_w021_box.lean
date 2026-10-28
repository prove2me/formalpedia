-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w021_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w021_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:44:31.273644+00:00
-- url     : https://prove2.me/theorems/d61ce073-a91f-4dc2-bc99-5ba212462bf8
-- title:
--   Diagonal Hlawka coordinate box on [405/64, 203/32]
-- statement:
--   Let $p\in[405/64,203/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=122357/50000$, $A=150279/100000$, and $d=84061/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(8609/50000)M_i$ for $h\ne i$. Then
--   $$-69979/100000\le X_{ii}\le-30063/50000,\qquad 83721/100000\le X_{ji}\le 4689/5000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w021_box (p : ℝ) (hpa : (405/64 : ℝ) ≤ p) (hpb : p ≤ (203/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (122357/50000 : ℝ) (150279/100000 : ℝ) (84061/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8609/50000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69979/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(30063/50000 : ℝ) else (83721/100000 : ℝ) ≤ X j i ∧ X j i ≤ (4689/5000 : ℝ) := by sorry
