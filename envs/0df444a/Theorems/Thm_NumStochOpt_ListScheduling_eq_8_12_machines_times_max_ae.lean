-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_eq_8_12_machines_times_max_ae
-- name    : NumStochOpt.ListScheduling.eq_8_12_machines_times_max_ae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T21:03:55.487591+00:00
-- url     : https://prove2.me/theorems/e0e3cac9-5963-4371-98d2-a1fd35250911
-- title:
--   Eq. (8.12) — $m\,p_{\max}/(n\mu) \to 0$ almost surely for $m = O(\sqrt n)$
-- statement:
--   Let $p_1, p_2, \dots$ be independent, identically distributed, nonnegative processing times on a probability space $(\Omega,\mathcal F,P)$ with mean $\mu > 0$ and $\mathbb E p_1^2 < \infty$, and let $p_{\max}^{(n)} = \max_{j\le n} p_j$. Let the number of machines $m = m(n) \ge 1$ depend on $n$ with $m(n) = O(\sqrt n)$. Then
--
--   $$
--   P\Bigl\{ \lim_{n\to\infty} \frac{m(n)\, p_{\max}^{(n)}}{n\mu} = 0 \Bigr\} = 1 .
--   $$
--
--   Together with the strong law (8.11) this makes both error terms of the sandwich (8.10) vanish almost surely.
--
--   **Formalization Note** The book writes "for all values of $m$ satisfying $m = 0(\sqrt n)$"; the printed zero is read as the big-O symbol, and $m$ as a function of $n$: `(fun n => (m n : ℝ)) =O[atTop] (fun n => √n)`, together with $m(n) \ge 1$. The statement asserts that almost surely the limit exists and equals $0$.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 206, Eq. (8.12) (model: p. 205)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace NumStochOpt.ListScheduling

/-- Eq. (8.12), p. 206: under the model of §8.2 (i.i.d. nonnegative processing times with mean
`μ > 0` and `E p₁² < ∞`), for machine counts `m(n) ≥ 1` with `m(n) = O(√n)`,
`m(n) p_max / (nμ) → 0` almost surely. -/
theorem eq_8_12_machines_times_max_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (m n : ℝ) * maxProcTime n (fun j => p j ω) / (n * μ))
      atTop (𝓝 0) := by sorry

end NumStochOpt.ListScheduling
