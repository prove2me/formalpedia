-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_positive_w040_box
-- name    : HlawkaSchatten.DiagonalCutoff6.positive_w040_box
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T19:51:00.514861+00:00
-- url     : https://prove2.me/theorems/b0d5a7d3-481a-4d48-8ee1-01923ba61ea2
-- title:
--   Diagonal Hlawka coordinate box on [109/16, 219/32]
-- statement:
--   Let $p\in[109/16,219/32]$ and let $X$ satisfy the normalized signed-coordinate constraints with $k=265919/100000$, $A=9207/6250$, and $d=17021/20000$. Write $V_i=\sum_{j\ne i}X_j$ and $M_i=(V_i)_i$. Assume all six tail coordinates are nonnegative and $|(V_i)_h|\le(1809/10000)M_i$ for $h\ne i$. Then
--   $$-14491/20000\le X_{ii}\le-2979/5000,\qquad 41617/50000\le X_{ji}\le 48059/50000\quad(j\ne i).$$
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Signed-tail majorant: https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a . Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff6.positive_w040_box (p : ℝ) (hpa : (109/16 : ℝ) ≤ p) (hpb : p ≤ (219/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (265919/100000 : ℝ) (9207/6250 : ℝ) (17021/20000 : ℝ) X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1809/10000 : ℝ)*pair X i i) :
    ∀ j i, if j=i then -(14491/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2979/5000 : ℝ) else (41617/50000 : ℝ) ≤ X j i ∧ X j i ≤ (48059/50000 : ℝ) := by sorry
