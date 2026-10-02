-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_eq_8_13_optimal_makespan_ratio_ae
-- name    : NumStochOpt.ListScheduling.eq_8_13_optimal_makespan_ratio_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:18:44.748185+00:00
-- url     : https://prove2.me/theorems/895fce75-1356-405d-9b1b-43e3cea0502b
-- title:
--   Eq. (8.13) — $C^*_n(m)/(n\mu/m) \to 1$ almost surely for $m = O(\sqrt n)$ machines
-- statement:
--   Consider the second stage of the machine investment problem. Let $p_1, p_2, \dots$ be independent, identically distributed, nonnegative processing times on a probability space $(\Omega, \mathcal F, P)$ with expected value $\mu > 0$ and $\mathbb E p_1^2 < \infty$; the instance with $n$ jobs uses $p_1, \dots, p_n$. Let the number of identical machines $m = m(n) \ge 1$ grow at most like $\sqrt n$: $m(n) = O(\sqrt n)$. Let $C^*_n(m)$ be the minimum makespan, the minimum over all assignments of the $n$ jobs to the $m$ machines of the largest machine load. Then
--
--   $$
--   P\Bigl\{ \lim_{n\to\infty} \frac{C^*_n(m)}{n\mu/m} = 1 \Bigr\} = 1 .
--   $$
--
--   The optimal value of an NP-hard second-stage problem is asymptotically the simple function $n\mu/m$ of the problem parameters and the first-stage decision $m$. This is what makes the first-stage estimate $Z'_n(m) = cm + n\mu/m$ of §8.3 legitimate.
--
--   **Formalization Note** The processing times are one sequence `p : ℕ → Ω → ℝ` (0-based), mutually independent (`iIndepFun`), measurable, identically distributed with `p 0`, pointwise nonnegative, with `p 0 ^ 2` integrable and `∫ p 0 = μ > 0`. Nonnegativity and $\mu > 0$ are not printed in the book but are implicit (processing times; the book divides by $n\mu$). The book's "m = 0(√n)" is read as $m(n) \ge 1$ and `(fun n => (m n : ℝ)) =O[atTop] (fun n => √n)`; a fixed $m$ would reduce the statement to the strong law. "$P\{\lim\dots = 1\} = 1$" is rendered as: almost surely the sequence converges to $1$.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 206, Eq. (8.13) (model: p. 205)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace NumStochOpt.ListScheduling

/-- Eq. (8.13), p. 206: under the model of §8.2 (i.i.d. nonnegative processing times with mean
`μ > 0` and `E p₁² < ∞`), for machine counts `m(n) ≥ 1` with `m(n) = O(√n)`, almost surely
`C*_n(m(n)) / (nμ/m(n)) → 1`, where `C*_n(m)` is the minimum makespan of the first `n` jobs on
`m` identical machines. -/
theorem eq_8_13_optimal_makespan_ratio_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => optMakespan n (m n) (fun j => p j ω) / (n * μ / m n))
      atTop (𝓝 1) := by sorry

end NumStochOpt.ListScheduling
