-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_Supplement_log_concave_mean_tail
-- name    : IndependentInfoPricing.Main.Supplement.log_concave_mean_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:53:23.548734+00:00
-- url     : https://prove2.me/theorems/552f18ac-0e3c-4932-8323-22ef759590ac
-- title:
--   Lemma 4.10 — Mean-tail bound for log-concave densities
-- statement:
--   Let $W\ge0$ have a log-concave density and finite mean $\mu=\mathbb E[W]$. Then
--   $$\Pr(W\ge\mu)\ge\frac1e .$$
--
--   The exponential distribution shows that the constant $1/e$ is sharp. In the proof of Theorem 4.7 it guarantees that a price equal to a conditional mean sells with conditional probability at least $1/e$.
--
--   **Formalization Note** The finite mean is integrability of the identity under the law of $W$, and $\mu$ is its Bochner integral; $1/e$ is `Real.exp (-1)`.
--
--   Differences from the source:
--   - encoding: real expected revenues, suprema and probabilities → nonnegative extended reals (ℝ≥0∞): lintegrals, suprema and measures; reason: the base mission's convention; it represents every finite value unchanged and avoids default-zero integrals
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.10, printed p.32 (PDF p.34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Supplement_LogConcave

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Lemma 4.10, p.32 (PDF 34): `W ≥ 0` with a log-concave density and finite mean `μ` has
`Pr(W ≥ μ) ≥ 1/e`. -/
theorem log_concave_mean_tail (W : Measure ℝ) [IsProbabilityMeasure W]
    (hW : LogConcaveDensity W) (hnn : W (Set.Iio 0) = 0) (hint : Integrable (fun x : ℝ => x) W) :
    ENNReal.ofReal (Real.exp (-1)) ≤ W (Set.Ici (∫ x, x ∂W)) := by sorry


end IndependentInfoPricing.Main.Supplement
