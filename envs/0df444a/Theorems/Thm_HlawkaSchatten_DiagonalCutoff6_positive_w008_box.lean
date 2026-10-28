-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w008_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w008_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:32:20.260119+00:00
-- url     : https://prove2.me/theorems/d206cc74-4c1e-46cd-bacd-07ab88f7178d
-- title:
--   Diagonal Hlawka coordinate box on [49/8, 393/64]
-- statement:
--   Let $p\in[49/8,393/64]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=117939/50000$, $A=6069/4000$, and $d=83579/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(8731/50000)M_i$ for $h\ne i$. Then
--   $$-34847/50000\le X_{ii}\le-29763/50000,\qquad 83123/100000\le X_{ji}\le 46791/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w008_box (p : ℝ) (hpa : (49/8 : ℝ) ≤ p) (hpb : p ≤ (393/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (117939/50000 : ℝ) (6069/4000 : ℝ) (83579/100000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8731/50000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(34847/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29763/50000 : ℝ) else (83123/100000 : ℝ) ≤ X j i ∧ X j i ≤ (46791/50000 : ℝ) := by sorry
