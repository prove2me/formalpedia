-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_ErgodicAux_ae_tendsto_average
-- name    : OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T18:32:48.717231+00:00
-- url     : https://prove2.me/theorems/e95b9a22-9d15-4d79-9304-c9ae3418b16e
-- title:
--   Birkhoff's pointwise ergodic theorem, ergodic case: Birkhoff averages of an integrable function converge almost everywhere to its integral
-- statement:
--   Let $\alpha$ be a type with a measurable space structure, and let $\mu$ be a probability measure on $\alpha$ (`IsProbabilityMeasure μ`). Let $T : \alpha \to \alpha$ be ergodic for $\mu$ (`Ergodic T μ`, Mathlib's notion: $T$ is measurable, $\mu$ is $T$-invariant (`MeasurePreserving T μ μ`), and every measurable set $s$ with $T^{-1}(s) = s$ is almost everywhere empty or almost everywhere everything, `EventuallyConst s (ae μ)`). Let $f : \alpha \to \mathbb R$ be measurable (`Measurable f`) and integrable for $\mu$ (`Integrable f μ`). Write $S_n f(x) = \sum_{k=0}^{n-1} f(T^k x)$ for the Birkhoff sum (Mathlib's `birkhoffSum T f n x`). Then for $\mu$-almost every $x$,
--   $$\frac{S_n f(x)}{n} \;\longrightarrow\; \int f \, d\mu \qquad (n \to \infty).$$
--   In Lean the quotient is `birkhoffSum T f n x / (n : ℝ)`, a real division, so the term for $n = 0$ is $0$; the limit is along `atTop` on the natural numbers, to `𝓝 (∫ x, f x ∂μ)`.
--
--   This is the ergodic case of Birkhoff's pointwise ergodic theorem (G. D. Birkhoff, 1931): for ergodic $T$, the invariant limit of the general theorem is the constant $\int f\,d\mu$.
--
--   Lean: `OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average`, OpenAI's theorem of that name (in `lean/OAI/MeasureTheory/SelfSimilar/ErgodicAverages.lean`), with the universe `uα` of $\alpha$ arbitrary. The statement uses only Mathlib's definitions (`Ergodic`, `birkhoffSum`, `Integrable`, `Measurable`, `IsProbabilityMeasure`) and imports no definitions bundle.
-- source:
--   G. D. Birkhoff, Proof of the ergodic theorem, Proc. Natl. Acad. Sci. USA 17 (1931), 656–660 (the theorem); proof and Lean code: OpenAI, The entropy-rate dimension formula for self-similar measures on the line, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 148; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/SelfSimilar/ErgodicAverages.lean (declaration OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_average)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace EntropyRateDimension
namespace ErgodicAux

variable {α : Type uα}

variable [MeasurableSpace α] {μ : Measure α}

theorem ae_tendsto_average [IsProbabilityMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / (n : ℝ)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  sorry

end ErgodicAux
end EntropyRateDimension

end

end OAI
end
