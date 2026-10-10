-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedSlicedForecastChildSize_upper
-- name    : OAI.Erdos3.VectorPolynomial.preparedSlicedForecastChildSize_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:37:31.827978+00:00
-- url     : https://prove2.me/theorems/3f98213c-6ccc-4e31-a53a-6297f852f467
-- title:
--   The sliced-forecast child size is at most exp(childLog + 1)
-- statement:
--   For every real number $\ell\ge0$ (`childLog`), `preparedSlicedForecastChildSize` $\ell$ (cast to $\mathbb R$) is at most $e^{\ell+1}$, where `preparedSlicedForecastChildSize` $\ell$ is the natural number $\lceil e^{\ell}\rceil$ (Mathlib's natural-number ceiling `⌈·⌉₊`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastChildSize_upper` in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean#L90

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastChildSize_upper {childLog : ℝ} (hchildLog : 0 ≤ childLog) :
    (preparedSlicedForecastChildSize childLog : ℝ) ≤ Real.exp (childLog + 1) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
