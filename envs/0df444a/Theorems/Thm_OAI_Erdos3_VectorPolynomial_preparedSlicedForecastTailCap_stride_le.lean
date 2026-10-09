-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedSlicedForecastTailCap_stride_le
-- name    : OAI.Erdos3.VectorPolynomial.preparedSlicedForecastTailCap_stride_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:49:33.155036+00:00
-- url     : https://prove2.me/theorems/2c03cb4d-ba43-4e9f-8aec-3d6bafcfd162
-- title:
--   The sliced-forecast tail cap is at least 2 exp(cost)
-- statement:
--   For every real number $c$ (`cost`), $2e^{c}\le$ `preparedSlicedForecastTailCap` $c$, where `preparedSlicedForecastTailCap` $c$ is the real number $\max(\texttt{preparedSlicedForecastPrimitiveCap},\,2e^{c})$ and `preparedSlicedForecastPrimitiveCap` is a real constant.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastTailCap_stride_le` in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean#L34

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastTailCap_stride_le (cost : ℝ) :
    2 * Real.exp cost ≤ preparedSlicedForecastTailCap cost := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
