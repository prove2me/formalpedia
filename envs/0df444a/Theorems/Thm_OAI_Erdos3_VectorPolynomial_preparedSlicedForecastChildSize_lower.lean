-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedSlicedForecastChildSize_lower
-- name    : OAI.Erdos3.VectorPolynomial.preparedSlicedForecastChildSize_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:25:37.070979+00:00
-- url     : https://prove2.me/theorems/c11534da-8f19-4c93-a66f-61bdf263e83f
-- title:
--   The sliced-forecast child size is at least exp(childLog)
-- statement:
--   For every real number $\ell$ (`childLog`), $e^{\ell}\le$ `preparedSlicedForecastChildSize` $\ell$ (cast to $\mathbb R$), where `preparedSlicedForecastChildSize` $\ell$ is the natural number $\lceil e^{\ell}\rceil$ (Mathlib's natural-number ceiling `⌈·⌉₊`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastChildSize_lower` in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean#L86

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastChildSize_lower (childLog : ℝ) :
    Real.exp childLog ≤ (preparedSlicedForecastChildSize childLog : ℝ) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
