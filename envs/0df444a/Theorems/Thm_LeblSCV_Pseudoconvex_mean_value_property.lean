-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_mean_value_property
-- name    : LeblSCV.Pseudoconvex.mean_value_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:03:55.62243+00:00
-- url     : https://prove2.me/theorems/2c1e777a-308f-4ebe-a594-7699130cbd87
-- title:
--   Proposition 2.4.3 — mean-value and sub-mean-value property
-- statement:
--   Let $U \subset \mathbb{C}$ be open, and write $\overline{\Delta_r(a)}$ for the closed disc of radius $r > 0$ about $a$.
--
--   (i) A continuous $f : U \to \mathbb{R}$ is harmonic if and only if
--   $$f(a) = \frac{1}{2\pi}\int_0^{2\pi} f(a + re^{i\theta})\,d\theta \qquad \text{whenever } \overline{\Delta_r(a)} \subset U.$$
--
--   (ii) An upper-semicontinuous $f : U \to \mathbb{R} \cup \{-\infty\}$ is subharmonic if and only if
--   $$f(a) \le \frac{1}{2\pi}\int_0^{2\pi} f(a + re^{i\theta})\,d\theta \qquad \text{whenever } \overline{\Delta_r(a)} \subset U.$$
--
--   The sub-mean-value property is the working form of subharmonicity. The later results of the chapter use it throughout: the maximum principle, suprema of families, smoothing, and the proof of Theorem 2.5.6.
--
--   **Formalization Note.** In (i) the mean is Mathlib's `Real.circleAverage f a r`. It is a Bochner integral, which is genuine here because $f$ is continuous on the circle. In (ii) the mean is the Lebesgue circle mean `circleMeanE` (positive minus negative part), because $f$ may take the value $-\infty$. The radius is required to be positive, as for the book's discs. Values in $\mathbb{R}\cup\{-\infty\}$ are modelled in `EReal` together with the requirement $f \neq +\infty$ on $U$; upper semicontinuity is Mathlib's `UpperSemicontinuousOn` for the order of `EReal`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 81, Proposition 2.4.3

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsHarmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_IsSubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_circleMeanE

namespace LeblSCV.Pseudoconvex

/-- Proposition 2.4.3 (Lebl, p. 81), mean-value and sub-mean-value property, for an open
`U ⊂ ℂ`. `closure Δ_r(a) = Metric.closedBall a r` with radius `r > 0`.
(i) A continuous `f : U → ℝ` is harmonic iff `f(a) = (1/2π) ∫₀^{2π} f(a + r e^{iθ}) dθ`
(`Real.circleAverage f a r`) whenever `closure Δ_r(a) ⊂ U`.
(ii) An upper-semicontinuous `f : U → ℝ ∪ {−∞}` is subharmonic iff
`f(a) ≤ (1/2π) ∫₀^{2π} f(a + r e^{iθ}) dθ` (Lebesgue integral, `circleMeanE`) whenever
`closure Δ_r(a) ⊂ U`. -/
theorem mean_value_property (U : Set ℂ) (hU : IsOpen U) :
    (∀ f : ℂ → ℝ, ContinuousOn f U →
      (IsHarmonicOn f U ↔
        ∀ (a : ℂ) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ U →
          f a = Real.circleAverage f a r)) ∧
    (∀ f : ℂ → EReal, UpperSemicontinuousOn f U → (∀ z ∈ U, f z ≠ ⊤) →
      (IsSubharmonicOn f U ↔
        ∀ (a : ℂ) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ U →
          f a ≤ circleMeanE f a r)) := by sorry

end LeblSCV.Pseudoconvex
