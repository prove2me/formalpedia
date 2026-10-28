-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w015_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w015_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:41:43.163718+00:00
-- url     : https://prove2.me/theorems/d875fd42-4e97-4bf6-8e94-dcd55074382e
-- title:
--   Diagonal Hlawka coordinate box on [399/64, 25/4]
-- statement:
--   Let $p\in[399/64,25/4]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=30079/12500$, $A=15093/10000$, and $d=41921/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1083/6250)M_i$ for $h\ne i$. Then
--   $$-13969/20000\le X_{ii}\le-59853/100000,\qquad 83453/100000\le X_{ji}\le 11711/12500\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w015_box (p : ℝ) (hpa : (399/64 : ℝ) ≤ p) (hpb : p ≤ (25/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30079/12500 : ℝ) (15093/10000 : ℝ) (41921/50000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1083/6250 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(13969/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59853/100000 : ℝ) else (83453/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11711/12500 : ℝ) := by sorry
