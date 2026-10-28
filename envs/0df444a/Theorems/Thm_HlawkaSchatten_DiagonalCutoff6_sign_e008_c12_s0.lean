-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_sign_e008_c12_s0
-- name    : HlawkaSchatten.DiagonalCutoff6.sign_e008_c12_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:33:28.758799+00:00
-- url     : https://prove2.me/theorems/0aa65066-25db-4268-9383-844978049b50
-- title:
--   Hlawka sign class 13, step 1, on [7, 57/8]
-- statement:
--   Let $p\in[7,57/8]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=274171/100000$, $A=146313/100000$, and $d=42737/50000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. The signs of $(V_0)_1,(V_0)_2,(V_1)_0,(V_1)_2,(V_2)_0,(V_2)_1$ are [0, 1, 1, 0, 1, 1], where 1 means nonnegative and 0 means nonpositive. Assume $|(V_i)_h|\le(1)M_i$ for $h\ne i$. Then $$|(V_i)_h|\le(21831/50000)M_i\quad(h\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.sign_e008_c12_s0 (p : ℝ) (hpa : (7 : ℝ) ≤ p) (hpb : p ≤ (57/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (274171/100000 : ℝ) (146313/100000 : ℝ) (42737/50000 : ℝ) X)
    (sign0 : (X 1 1+X 2 1) ≤ 0)
    (sign1 : 0 ≤ (X 1 2+X 2 2))
    (sign2 : 0 ≤ (X 0 0+X 2 0))
    (sign3 : (X 0 2+X 2 2) ≤ 0)
    (sign4 : 0 ≤ (X 0 0+X 1 0))
    (sign5 : 0 ≤ (X 0 1+X 1 1))
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1 : ℝ)*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ (21831/50000 : ℝ)*pair X i i := by sorry
