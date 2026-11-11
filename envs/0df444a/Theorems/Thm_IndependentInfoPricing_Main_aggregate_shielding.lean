-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_aggregate_shielding
-- name    : IndependentInfoPricing.Main.aggregate_shielding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:15.979193+00:00
-- url     : https://prove2.me/theorems/bcbcdfed-f607-4245-825d-dbde340ae2f8
-- title:
--   Lemma 4.16 — Aggregate shielding
-- statement:
--   Let $W_1,\ldots,W_m\ge0$ be independent and put $a_i=\operatorname{Rev}(W_i)$, $M=\sum_i a_i$. Suppose each coordinate obeys the half-tail property $\Pr(W_i\ge a_i)\ge1/2$. Then
--
--   $$\Pr\!\left(\sum_i W_i\ge\frac M2\right)\ge\frac12.$$
--
--   There is no regularity or finite-mean hypothesis; revenue thresholds and the event are expressed in nonnegative extended reals, so infinite revenues cannot be replaced by default zero. The empty block has total zero and the event is certain. This is the shielding input for the two conditional magnitude blocks.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.16, printed pp.40–40 (PDF pp.42–42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.16, p.40 (PDF 42), (66); no regularity or finite mean. -/
theorem aggregate_shielding {m : ℕ} (W : Marginals (Fin m)) (hW : nonnegativeLaws W)
    (hhalf : ∀ i, HalfTail (W i)) :
    (1 / 2 : ℝ≥0∞) ≤ productLaw W {v | (∑ i, scalarRevenue (W i)) / 2 ≤ ENNReal.ofReal (∑ i, v i)} := by sorry

end IndependentInfoPricing.Main
