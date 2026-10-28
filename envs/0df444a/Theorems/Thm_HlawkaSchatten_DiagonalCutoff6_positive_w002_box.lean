-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w002_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w002_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:06:57.332573+00:00
-- url     : https://prove2.me/theorems/a8582e9d-993d-4c04-9166-1c1ff14c90f0
-- title:
--   Diagonal Hlawka coordinate box on [193/32, 387/64]
-- statement:
--   Let $p\in[193/32,387/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=231811/100000$, $A=30489/20000$, and $d=41673/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(17579/100000)M_i$ for $h\ne i$. Then\n$$-69571/100000\le X_{ii}\le-59239/100000,\qquad 82827/100000\le X_{ji}\le 23373/25000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w002_box (p : ℝ) (hpa : (193/32 : ℝ) ≤ p) (hpb : p ≤ (387/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (231811/100000 : ℝ) (30489/20000 : ℝ) (41673/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17579/100000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(69571/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59239/100000 : ℝ) else (82827/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23373/25000 : ℝ) := by sorry
