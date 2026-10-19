-- Prove2me | Theorems.Thm_LargeBSP_Homog_empQuantile_tendstoInMeasure
-- name    : LargeBSP.Homog.empQuantile_tendstoInMeasure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:00.160157+00:00
-- url     : https://prove2.me/theorems/2cbd0c5f-93ac-4d29-beb4-801cc381a1dd
-- title:
--   Proof of Theorem 2, p. A2 — 𝔽^{-1}_{X,N}(u) ⇒ F_X^{-1}(u) at continuity points u ∈ (0,1)
-- statement:
--   Let $X_1, X_2, \dots \ge 0$ be measurable valuations whose empirical cdfs satisfy $\mathbb F_{X,N}(y) \Rightarrow F_X(y)$ for every $y \ge 0$ (Assumption 1), where $F_X$ is the distribution function of a nonnegative random variable with finite mean. Then for every $u \in (0,1)$ at which $F_X^{-1}$ is continuous,
--   $$\mathbb F^{-1}_{X,N}(u) \Rightarrow F_X^{-1}(u) \qquad (N \to \infty).$$
--
--   This is the empirical-quantile analogue of Lemma 21.2 of van der Vaart (2000) under Assumption 1.
--
--   **Formalization Note** $\Rightarrow$ is convergence in probability; continuity is of the function $u \mapsto F_X^{-1}(u)$ at $u$.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 2 (Appendix A.1), p. A2, sentence before (A7)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- Proof of Theorem 2, p. A2: under Assumption 1, `𝔽⁻¹_{X,N}(u) ⇒ F_X⁻¹(u)` for every
`u ∈ (0,1)` at which `F_X⁻¹` is continuous. -/
theorem empQuantile_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, ContinuousAt (quantile (cdf ν)) u →
      TendstoInMeasure P (fun (N : ℕ) ω => quantile (empCdf (fun n => X n ω) N) u) atTop
        (fun _ => quantile (cdf ν) u) := by sorry

end LargeBSP.Homog
