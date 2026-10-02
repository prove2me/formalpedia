-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_p207_expected_makespan_ratio
-- name    : NumStochOpt.ListScheduling.p207_expected_makespan_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:08:42.846131+00:00
-- url     : https://prove2.me/theorems/600204f7-a605-4536-a149-6804a18ac02d
-- title:
--   p. 207 — $\mathbb E C^*_n(m)/(n\mu/m) \to 1$ for $m = O(\sqrt n)$
-- statement:
--   Let $p_1, p_2, \dots$ be independent, identically distributed, nonnegative processing times with mean $\mu > 0$ and $\mathbb E p_1^2 < \infty$, and let $m = m(n) \ge 1$ with $m(n) = O(\sqrt n)$. Let $C^*_n(m)$ be the minimum makespan of the first $n$ jobs on $m$ identical machines. Then
--
--   $$
--   \lim_{n\to\infty} \frac{\mathbb E\, C^*_n(m)}{n\mu/m} = 1 .
--   $$
--
--   So the second-stage expected cost in $Z_n(m) = cm + \mathbb E C^*_n(m)$ of (8.9) is asymptotic to $n\mu/m$, which is what justifies the first-stage estimate $Z'_n(m) = cm + n\mu/m$ of §8.3.
--
--   **Formalization Note** $\mathbb E\, C^*_n(m)$ is the Bochner integral of $\omega \mapsto C^*_n(m(n))$ evaluated at the realized processing times; that function is measurable and bounded by $p_1 + \dots + p_n$, hence integrable. The book's "m = 0(√n)" is read as in (8.12).
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 207, unnumbered display following (8.13) (model: p. 205)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace NumStochOpt.ListScheduling

/-- p. 207, unnumbered display: under the model of §8.2 (i.i.d. nonnegative processing times
with mean `μ > 0` and `E p₁² < ∞`), for machine counts `m(n) ≥ 1` with `m(n) = O(√n)`,
`E C*_n(m(n)) / (nμ/m(n)) → 1`. -/
theorem p207_expected_makespan_ratio {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    Tendsto
      (fun n : ℕ => (∫ ω, optMakespan n (m n) (fun j => p j ω) ∂P) / (n * μ / m n))
      atTop (𝓝 1) := by sorry

end NumStochOpt.ListScheduling
