-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_totalL_interior
-- name    : MultiwayGap2325.Main.Supplement.affine_totalL_interior
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:02:07.056798+00:00
-- url     : https://prove2.me/theorems/e5ddf503-e58d-4ea5-bf92-bf4d8eda7fef
-- title:
--   Fractional cost of the affine weighting
-- statement:
--   For the affine weighting with $q\ge2$ and $T\in(1/2,1)$, the actual fractional cost decomposes as
--
--   $$
--   L=(1-T)B+\sum_{r=2}^{q}\frac{(rT-1)(1-r(1-T)^{r-1})}{2(r-1)(r-1)!\,T^{r-2}}.
--   $$
--
--   A face of cardinality $r$ has $\binom r2$ directions, each of constant weight $a_r/(r-1)$, and its truncated-face volume is $(1-r(1-T)^{r-1})/(r-1)!$. Multiplication by $\binom qr$ and substitution of $a_r$ give the interior sum, while the terminal contribution remains $(1-T)B$.
--
--   **Formalization Note** Both `totalL` and `totalB` on the right-hand side are evaluated from the same raw affine weighting.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, values paragraph and equation (25), p.24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.24: actual total L, split into terminal and interior contributions. -/
theorem affine_totalL_interior (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    totalL T (affineData q T).weighting =
      (1 - T) * totalB T (affineData q T).weighting + affineInteriorClosed q T := by sorry
