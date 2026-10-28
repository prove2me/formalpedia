-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w038_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w038_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:50:25.943478+00:00
-- url     : https://prove2.me/theorems/15ac5cb6-f85a-46ff-a1c5-989f00d67ae0
-- title:
--   Diagonal Hlawka coordinate box on [27/4, 217/32]
-- statement:
--   Let $p\in[27/4,217/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=263173/100000$, $A=147663/100000$, and $d=42489/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(18177/100000)M_i$ for $h\ne i$. Then
--   $$-72379/100000\le X_{ii}\le-59391/100000,\qquad 83063/100000\le X_{ji}\le 96087/100000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w038_box (p : ℝ) (hpa : (27/4 : ℝ) ≤ p) (hpb : p ≤ (217/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (263173/100000 : ℝ) (147663/100000 : ℝ) (42489/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18177/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(72379/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59391/100000 : ℝ) else (83063/100000 : ℝ) ≤ X j i ∧ X j i ≤ (96087/100000 : ℝ) := by sorry
