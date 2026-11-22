-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_flow_integral_values
-- name    : MultiwayGap2325.Main.Supplement.affine_flow_integral_values
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:18:38.305164+00:00
-- url     : https://prove2.me/theorems/023f80fe-d273-4dc3-8ca4-f54038769129
-- title:
--   Actual affine integrals for terminal mass, allowance and cost
-- statement:
--   Let $q\ge2$ and $T\in(1/2,1)$. Evaluating the actual face and facet integrals for the affine data gives
--
--   $$
--   B=\sum_{r=2}^{q}\frac{(rT-1)z^{r-2}}{(r-1)!},
--   \qquad z=\frac{1-T}{T},
--   $$
--
--   $$
--   R=\frac{1-q(1-T)^{q-1}}{q!\,T^{q-2}},
--   $$
--
--   and
--
--   $$
--   L=(1-T)B+\sum_{r=2}^{q}
--   \frac{(rT-1)(1-r(1-T)^{r-1})}{2(r-1)(r-1)!\,T^{r-2}}.
--   $$
--
--   These identities follow from the face counts $\binom qr$, the truncated-face volumes $(1-r(1-T)^{r-1})/(r-1)!$, the terminal-facet measures $(1-T)^{r-2}/(r-2)!$, and the constant densities in (23)–(24). Only the top face contributes to $R$, and its allowance is integrated once.
--
--   **Formalization Note** Each left-hand side is the platform's actual `totalB`, `totalR`, or `totalL` applied to `affineData q T`; no closed-form integral is built into the raw construction.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, values paragraph and equation (25), p.24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.24: the actual integrals defining B, R and L satisfy their respective formulas in (25). -/
theorem affine_flow_integral_values (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    totalB T (affineData q T).weighting = affineBSum q T ∧
    totalR T (affineData q T) = affineRClosed q T ∧
    totalL T (affineData q T).weighting =
      (1 - T) * totalB T (affineData q T).weighting + affineInteriorClosed q T := by sorry
