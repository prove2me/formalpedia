-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_totalB_sum
-- name    : MultiwayGap2325.Main.Supplement.affine_totalB_sum
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:58:29.30531+00:00
-- url     : https://prove2.me/theorems/4ff351b3-392c-474d-8178-50b5d9eddf39
-- title:
--   Terminal mass of the affine flow instance
-- statement:
--   For $q\ge2$ and $T\in(1/2,1)$, the actual integrated terminal-edge mass of the affine data is
--
--   $$
--   B=\sum_{r=2}^{q}\frac{(rT-1)z^{r-2}}{(r-1)!},
--   \qquad z=\frac{1-T}{T}.
--   $$
--
--   There are $\binom qr$ faces of cardinality $r$; each has $r$ terminal facets, and each terminal facet has measure $(1-T)^{r-2}/(r-2)!$. Multiplying these geometric factors by the constant terminal density $a_r$ and substituting (23) gives the displayed sum.
--
--   **Formalization Note** The left-hand side is `totalB` evaluated using the actual `facetMeasure` integrals, not a postulated formula.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), proof of Theorem 6.1, values paragraph, equation (25), p.24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.24, first expression for B in equation (25), evaluated from the actual facet integrals. -/
theorem affine_totalB_sum (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    totalB T (affineData q T).weighting = affineBSum q T := by sorry
