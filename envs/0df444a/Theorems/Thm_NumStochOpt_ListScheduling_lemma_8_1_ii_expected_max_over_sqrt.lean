-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_lemma_8_1_ii_expected_max_over_sqrt
-- name    : NumStochOpt.ListScheduling.lemma_8_1_ii_expected_max_over_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:05:28.80306+00:00
-- url     : https://prove2.me/theorems/a9267f14-1c54-491e-ac39-97254334e80d
-- title:
--   Lemma 8.1 (ii) — $\mathbb E p_{\max}/\sqrt n \to 0$ when $\mathbb E p_1^2 < \infty$
-- statement:
--   Let $p_1, p_2, \dots$ be independent, identically distributed, nonnegative random variables with $\mathbb E p_1^2 < \infty$, and let $p_{\max}^{(n)} = \max_{j=1,\dots,n} p_j$. Then
--
--   $$
--   \lim_{n\to\infty} \frac{\mathbb E\, p_{\max}^{(n)}}{\sqrt n} = 0 .
--   $$
--
--   This is the expectation counterpart of Lemma 8.1 (i); it controls the error term of (8.10) after taking expectations. The book states it without proof and refers to Feller.
--
--   **Formalization Note** $\mathbb E\, p_{\max}^{(n)}$ is the Bochner integral `∫ ω, maxProcTime n (fun j => p j ω) ∂P`; the maximum is integrable since it is measurable and bounded by $p_1 + \dots + p_n$. The other conventions are those of Lemma 8.1 (i).
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 206, Lemma 8.1 (ii) (model: p. 205)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

open MeasureTheory ProbabilityTheory Filter Topology

namespace NumStochOpt.ListScheduling

/-- Lemma 8.1 (ii), p. 206: if the processing times `p 0, p 1, …` are i.i.d., nonnegative, with
`E p₁² < ∞`, then `E p_max / √n → 0`, `p_max = max_{j<n} p j`. -/
theorem lemma_8_1_ii_expected_max_over_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P) :
    Tendsto (fun n : ℕ => (∫ ω, maxProcTime n (fun j => p j ω) ∂P) / Real.sqrt n)
      atTop (𝓝 0) := by sorry

end NumStochOpt.ListScheduling
