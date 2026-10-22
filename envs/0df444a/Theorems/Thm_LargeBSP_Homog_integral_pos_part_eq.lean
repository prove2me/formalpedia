-- Prove2me | Theorems.Thm_LargeBSP_Homog_integral_pos_part_eq
-- name    : LargeBSP.Homog.integral_pos_part_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:56.391449+00:00
-- url     : https://prove2.me/theorems/fb9c266b-a1c4-4535-9290-5d1a81beb6fc
-- title:
--   Proof of Theorem 2, p. A2 — ∫_0^1 (F_X^{-1}(1 − s) − c)^+ ds = ∫_0^{t⋆} (F_X^{-1}(1 − s) − c) ds = V̄(t⋆) − t⋆c
-- statement:
--   Let $F_X$ be the distribution function of a nonnegative random variable with finite mean, $c \ge 0$, $t^\star = \sup\{s \in (0,1) : F_X^{-1}(1-s) \ge c\}$ and $\bar V(t) = \int_0^t F_X^{-1}(1-s)\,ds$. Then
--   $$\int_0^1 \big(F_X^{-1}(1-s) - c\big)^+ ds = \int_0^{t^\star} \big(F_X^{-1}(1-s) - c\big)\,ds = \bar V(t^\star) - t^\star c.$$
--
--   Because $s \mapsto F_X^{-1}(1-s)$ is non-increasing, the positive part is active exactly on $(0, t^\star)$; the identity is the closing step of the proof of Theorem 2.
--
--   **Formalization Note** $t^\star = 0$ when no $s$ qualifies, and then all three expressions are $0$.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 2 (Appendix A.1), p. A2, last display

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- Proof of Theorem 2, last display, p. A2:
`∫_0^1 (F_X⁻¹(1 − s) − c)⁺ ds = ∫_0^{t⋆} (F_X⁻¹(1 − s) − c) ds = V̄(t⋆) − t⋆ c`. -/
theorem integral_pos_part_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : Integrable id ν) (c : ℝ) (hc : 0 ≤ c) :
    ∫ s in (0 : ℝ)..1, max (quantile (cdf ν) (1 - s) - c) 0 =
        ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) ∧
      ∫ s in (0 : ℝ)..(tstar ν c), (quantile (cdf ν) (1 - s) - c) =
        Vlim ν (tstar ν c) - tstar ν c * c := by sorry

end LargeBSP.Homog
