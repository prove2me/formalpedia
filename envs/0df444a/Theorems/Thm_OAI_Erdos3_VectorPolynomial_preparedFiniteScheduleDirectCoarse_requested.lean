-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteScheduleDirectCoarse_requested
-- name    : OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectCoarse_requested
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T08:03:00.779008+00:00
-- url     : https://prove2.me/theorems/eb5ebae9-3ebb-44aa-b6e3-7036b9d9ee79
-- title:
--   The direct coarse schedule parameter is at least the requested coarse value
-- statement:
--   Let $K$ be a finite type, $\mathrm{gainLog} : K \to \mathbb R$ and $\mathrm{requestedCoarse} \in \mathbb R$. Then
--   $$\mathrm{requestedCoarse} \le \texttt{preparedFiniteScheduleDirectCoarse gainLog requestedCoarse},$$
--   where `preparedFiniteScheduleDirectCoarse gainLog requestedCoarse` $= \max\bigl(\sum_{k \in K}(\mathrm{gainLog}(k) + 32),\ \mathrm{requestedCoarse}\bigr)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedFiniteScheduleDirectCoarse_requested` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B187` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleLocalScalarConstruction.lean#L287

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B187

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleDirectCoarse_requested {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) :
    requestedCoarse ≤ preparedFiniteScheduleDirectCoarse gainLog requestedCoarse := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
