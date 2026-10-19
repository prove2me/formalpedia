-- Prove2me | Theorems.Thm_LargeBSP_Homog_eq_A7
-- name    : LargeBSP.Homog.eq_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:53.863988+00:00
-- url     : https://prove2.me/theorems/40702309-88ae-4d3a-a9a6-e1e5cf0cbd3b
-- title:
--   (A7), p. A2 — V̄_N(1) − V̄_N(t) ⇒ ∫_t^1 F_X^{-1}(1 − s) ds for t ∈ (0,1]
-- statement:
--   Let $X_1, X_2, \dots \ge 0$ be measurable valuations with $\mathbb F_{X,N}(y) \Rightarrow F_X(y)$ for every $y \ge 0$ (Assumption 1), $F_X$ the distribution function of a nonnegative random variable with finite mean. Then for each $t \in (0,1]$,
--   $$\bar V_N(1) - \bar V_N(t) \Rightarrow \int_t^1 F_X^{-1}(1-s)\,ds \qquad (N \to \infty).$$
--
--   The left side is the normalized value of the items outside the top $\lfloor Nt \rfloor$; together with (A6) it gives the convergence $\bar V_N(t) \Rightarrow \bar V(t)$ of Theorem 2.
--
--   **Formalization Note** $\Rightarrow$ is convergence in probability. Only Assumption 1 is assumed, as on the page. The page's middle expression $\int_t^1 \mathbb F^{-1}_{X,N}(1-s)\,ds$ equals the left side only at grid points (see the companion statement on $\bar V_N(n/N)$); only the convergence is stated.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 2 (Appendix A.1), p. A2, (A7)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- (A7), p. A2: under Assumption 1, for each `t ∈ (0,1]`,
`V̄_N(1) − V̄_N(t) ⇒ ∫_t^1 F_X⁻¹(1 − s) ds`. -/
theorem eq_A7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => Vbar (fun n => X n ω) N 1 - Vbar (fun n => X n ω) N t) atTop
      (fun _ => ∫ s in t..1, quantile (cdf ν) (1 - s)) := by sorry

end LargeBSP.Homog
