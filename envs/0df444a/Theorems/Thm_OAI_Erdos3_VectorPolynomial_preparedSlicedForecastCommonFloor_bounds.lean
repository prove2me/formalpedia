-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedSlicedForecastCommonFloor_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloor_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:03:38.641023+00:00
-- url     : https://prove2.me/theorems/17fc205c-eb3b-4877-b25b-f78c596e30ba
-- title:
--   Bounds on the common floor of the sliced-forecast comparison
-- statement:
--   Let $p,\ell,c,q$ be real numbers (`periodLog`, `childLog`, `cost`, `comparisonLog`). Write $F=$ `preparedSlicedForecastCommonFloorExponent p ℓ c q` $=\max(0,p,\ell,c+1,q)$ and $L_{\min}=$ `preparedSlicedForecastCommonFloor p ℓ c q` $=\lceil e^{F}\rceil\in\mathbb N$. Then: $0\le F$; $0<L_{\min}$; $L_{\min}\le e^{F+1}$; `preparedSlicedForecastChildSize` $\ell$ $\le L_{\min}$, where `preparedSlicedForecastChildSize` $\ell=\lceil e^{\ell}\rceil$; $2e^{c}\le L_{\min}$; every natural number $T$ with $T\le e^{p}$ satisfies $T\le L_{\min}$; and every natural number $L$ with $L\le e^{q}$ satisfies $L\le L_{\min}$. (Here $\lceil\cdot\rceil$ is Mathlib's natural-number ceiling `⌈·⌉₊`.)
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloor_bounds` in `lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/PreparedSlicedForecastComparisonLogs.lean#L134

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastCommonFloor_bounds
    (periodLog childLog cost comparisonLog : ℝ) :
    let F := preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog
    let Lmin := preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog
    0 ≤ F ∧ 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (F + 1) ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
