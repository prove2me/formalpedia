-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_sign_e002_c09_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.sign_e002_c09_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:16:05.628808+00:00
-- url     : https://prove2.me/theorems/236ed6e4-b1d4-4e32-b7a9-4001b8bf83a5
-- title:
--   Hlawka sign class 10, step 2, on [25/4, 51/8]
-- statement:
--   Let $p\in[25/4,51/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=7541/3125$, $A=150819/100000$, and $d=83879/100000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. The signs of $(V_0)_1,(V_0)_2,(V_1)_0,(V_1)_2,(V_2)_0,(V_2)_1$ are [0, 1, 0, 1, 0, 1], where 1 means nonnegative and 0 means nonpositive. Assume $|(V_i)_h|\le(6789/12500)M_i$ for $h\ne i$. These conditions are inconsistent.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.sign_e002_c09_s1 (p : ℝ) (hpa : (25/4 : ℝ) ≤ p) (hpb : p ≤ (51/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7541/3125 : ℝ) (150819/100000 : ℝ) (83879/100000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : (X 0 0+X 1 0) ≤ 0)
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6789/12500 : ℝ)*pair X i i) :
    False := by sorry
