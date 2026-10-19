-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_ErgodicAux_ae_tendsto_triangle
-- name    : OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T18:32:47.433993+00:00
-- url     : https://prove2.me/theorems/9ceca243-8148-4e1a-ba7c-727b6ab195be
-- title:
--   Maker's generalized ergodic theorem, ergodic case: averages of a dominated a.e.-convergent sequence along an ergodic orbit converge a.e. to the integral of the limit
-- statement:
--   Let $\alpha$ be a type with a measurable space structure, and let $\mu$ be a probability measure on $\alpha$ (`IsProbabilityMeasure μ`). Let $T : \alpha \to \alpha$ be ergodic for $\mu$ (`Ergodic T μ`, Mathlib's notion: $T$ is measurable, $\mu$ is $T$-invariant (`MeasurePreserving T μ μ`), and every measurable set $s$ with $T^{-1}(s) = s$ satisfies `EventuallyConst s (ae μ)`). Let $f_n : \alpha \to \mathbb R$ ($n \in \mathbb N$, `f : ℕ → α → ℝ`), $g : \alpha \to \mathbb R$ and $F : \alpha \to \mathbb R$ be functions such that:
--   - every $f_n$, $g$ and $F$ is measurable (`∀ n, Measurable (f n)`, `Measurable g`, `Measurable F`);
--   - $|f_n(x)| \le F(x)$ for all $n$ and all $x$, and $|g(x)| \le F(x)$ for all $x$;
--   - $F$ is integrable for $\mu$ (`Integrable F μ`);
--   - $f_n(x) \to g(x)$ as $n \to \infty$ for $\mu$-almost every $x$.
--
--   Then for $\mu$-almost every $x$,
--   $$\frac{1}{n}\sum_{j=0}^{n-1} f_{n-j}\bigl(T^j x\bigr) \;\longrightarrow\; \int g \, d\mu \qquad (n \to \infty).$$
--   In Lean the average is `(∑ j ∈ Finset.range n, f (n - j) (T^[j] x)) / (n : ℝ)`, where `n - j` is natural-number subtraction (here $j < n$, so it is the ordinary difference) and `T^[j]` is the $j$-th iterate of $T$; the division is real division, so the term for $n = 0$ is $0$; the limit is along `atTop` on the natural numbers, to `𝓝 (∫ x, g x ∂μ)`.
--
--   This is the ergodic case of Maker's generalization of Birkhoff's ergodic theorem to sequences of functions (P. T. Maker, 1940). Taking $f_n = g$ for all $n$ and $F = |g|$ recovers the ergodic case of Birkhoff's theorem.
--
--   Lean: `OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle`, OpenAI's theorem of that name (in `lean/OAI/MeasureTheory/SelfSimilar/TriangularAverages.lean`), with the universe `uα` of $\alpha$ arbitrary. The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   P. T. Maker, The ergodic theorem for a sequence of functions, Duke Math. J. 6 (1940), 27–30 (the theorem); proof and Lean code: OpenAI, The entropy-rate dimension formula for self-similar measures on the line, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 148; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/SelfSimilar/TriangularAverages.lean (declaration OAI.EntropyRateDimension.ErgodicAux.ae_tendsto_triangle)

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
namespace EntropyRateDimension.ErgodicAux

variable {α : Type uα}

variable [MeasurableSpace α] {μ : Measure α}

 theorem ae_tendsto_triangle [IsProbabilityMeasure μ] {T : α → α}
    (hT : Ergodic T μ) {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g) (hFm : Measurable F)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (hF : Integrable F μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (∑ j ∈ Finset.range n, f (n-j) (T^[j] x)) / (n : ℝ))
      atTop (𝓝 (∫ x, g x ∂μ)) := by
  sorry

end EntropyRateDimension.ErgodicAux

end

end OAI
end
