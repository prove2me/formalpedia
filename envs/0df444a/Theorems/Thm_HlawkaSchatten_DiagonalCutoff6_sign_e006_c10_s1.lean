-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_sign_e006_c10_s1
-- name    : HlawkaSchatten.DiagonalCutoff6.sign_e006_c10_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:30:25.730976+00:00
-- url     : https://prove2.me/theorems/3331a7d1-8ff2-4a57-924d-08653c6a982a
-- title:
--   Hlawka sign class 11, step 2, on [27/4, 55/8]
-- statement:
--   Let $p\in[27/4,55/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=263173/100000$, $A=147663/100000$, and $d=42489/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. The signs of $(V_0)_1,(V_0)_2,(V_1)_0,(V_1)_2,(V_2)_0,(V_2)_1$ are [0, 1, 0, 1, 1, 1], where 1 means nonnegative and 0 means nonpositive. Assume $|(V_i)_h|\le(47507/100000)M_i$ for $h\ne i$. These conditions are inconsistent.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.sign_e006_c10_s1 (p : ℝ) (hpa : (27/4 : ℝ) ≤ p) (hpb : p ≤ (55/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (263173/100000 : ℝ) (147663/100000 : ℝ) (42489/50000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : (X 0 0+X 2 0) ≤ 0)
    (sign3 : 0 ≤ (X 0 2+X 2 2))
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (47507/100000 : ℝ)*pair X i i) :
    False := by sorry
