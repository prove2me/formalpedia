-- Prove2me | Theorems.Thm_MultiItemRev_KBundling_proposition_11
-- name    : MultiItemRev.KBundling.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:04.406731+00:00
-- url     : https://prove2.me/theorems/196fb17b-b46f-46c6-8b0d-57edfcec921c
-- title:
--   Proposition 11, p. 21 — monotonicity for one good: X dominated by Y implies Rev(X) ≤ Rev(Y)
-- statement:
--   **Proposition 11 (Monotonicity for One Good).** Let $X$ and $Y$ be one-good random valuations with laws $\nu$ and $\nu'$. If $X$ is stochastically dominated by $Y$, then
--   $$\mathrm{Rev}(X)\le\mathrm{Rev}(Y).$$
--
--   Revenue is monotone in the valuation for one good (unlike for several goods). This is what lets the one-good revenues in the bundling arguments be bounded by those of ER goods.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 21, Proposition 11

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KBundling

theorem proposition_11 (ν ν' : Measure ℝ≥0)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : MultiItemRev.KSeparate.StochDominated ν ν') : MultiItemRev.Decomp.Rev1 ν ≤ MultiItemRev.Decomp.Rev1 ν' := by sorry

end MultiItemRev.KBundling
