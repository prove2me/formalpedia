-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w017_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w017_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:42:52.110012+00:00
-- url     : https://prove2.me/theorems/42820a0f-041c-443c-9f10-c662b0bfce9b
-- title:
--   Diagonal Hlawka coordinate box on [401/64, 201/32]
-- statement:
--   Let $p\in[401/64,201/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=30249/12500$, $A=37677/25000$, and $d=20979/25000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17291/100000)M_i$ for $h\ne i$. Then
--   $$-69889/100000\le X_{ii}\le-11989/20000,\qquad 83543/100000\le X_{ji}\le 46859/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w017_box (p : ℝ) (hpa : (401/64 : ℝ) ≤ p) (hpb : p ≤ (201/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30249/12500 : ℝ) (37677/25000 : ℝ) (20979/25000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17291/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11989/20000 : ℝ) else (83543/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46859/50000 : ℝ) := by sorry
