-- Prove2me | Theorems.Thm_LargeBSP_Homog_eq_A6
-- name    : LargeBSP.Homog.eq_A6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:44.919032+00:00
-- url     : https://prove2.me/theorems/e410516e-e476-4ba5-90bb-eac76617f817
-- title:
--   (A6), p. A2 — V̄_N(1) ⇒ µ = ∫_0^1 F_X^{-1}(1 − s) ds
-- statement:
--   Let $X_1, X_2, \dots \ge 0$ be measurable valuations with $\frac1N \sum_{n=1}^N X_n \Rightarrow \mu$ (the weak law of Assumption 2), where $\mu$ is the (finite) mean of a distribution function $F_X$ of a nonnegative random variable. Then
--   $$\bar V_N(1) \Rightarrow \mu = \int_0^1 F_X^{-1}(1-s)\,ds \qquad (N \to \infty).$$
--
--   The first part identifies the normalized pure-bundle value with the sample average; the second is the identity "mean = integral of the quantile function".
--
--   **Formalization Note** $\Rightarrow$ is convergence in probability. $F_X$ is `cdf ν` with `ν` a probability measure on $\mathbb R$ giving no mass to $(-\infty, 0)$ and integrable identity; $\mu = \int y\,d\nu(y)$.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 2 (Appendix A.1), p. A2, (A6)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- (A6), p. A2: `V̄_N(1) ⇒ µ = ∫_0^1 F_X⁻¹(1 − s) ds` (the equality: the mean of `F_X` is the
integral of its quantile function). -/
theorem eq_A6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν)) :
    TendstoInMeasure P (fun (N : ℕ) ω => Vbar (fun n => X n ω) N 1) atTop (fun _ => ∫ y, y ∂ν) ∧
    ∫ y, y ∂ν = ∫ s in (0 : ℝ)..1, quantile (cdf ν) (1 - s) := by sorry

end LargeBSP.Homog
