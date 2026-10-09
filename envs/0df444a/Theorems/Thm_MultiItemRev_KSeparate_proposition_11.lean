-- Prove2me | Theorems.Thm_MultiItemRev_KSeparate_proposition_11
-- name    : MultiItemRev.KSeparate.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:37.291654+00:00
-- url     : https://prove2.me/theorems/62bd2c10-914e-4f69-ac4f-cac2b2815358
-- title:
--   Proposition 11, p. 21 — monotonicity of one-good revenue
-- statement:
--   Let $X$ and $Y$ be nonnegative one-good random valuations. If $X$ is first-order stochastically dominated by $Y$, meaning $\Pr[X\ge p]\le\Pr[Y\ge p]$ for every threshold $p$, then
--
--   $$\operatorname{Rev}(X)\le\operatorname{Rev}(Y).$$
--
--   This permits one-good revenue comparisons after replacing a valuation by a stochastically larger one. **Formalization Note** Thresholds are nonnegative because both laws are supported on nonnegative values; negative thresholds give equal tail probability one.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 21, Proposition 11

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.KSeparate

theorem proposition_11 (ν ν' : Measure ℝ≥0)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : StochDominated ν ν') : MultiItemRev.Decomp.Rev1 ν ≤ MultiItemRev.Decomp.Rev1 ν' := by sorry

end MultiItemRev.KSeparate
