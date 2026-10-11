-- Prove2me | Theorems.Thm_KPZBallistic_sudijono_thm_1_1_concentration
-- name    : KPZBallistic.sudijono_thm_1_1_concentration
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:31:48.13299+00:00
-- url     : https://prove2.me/theorems/5e40a169-72e6-4ecb-8370-d37d9b88cff7
-- title:
--   Sudijono Thm. 1.1 (2): concentration of $\xi_t(0)$ on scale $\sqrt t$
-- statement:
--   In one-dimensional nearest-neighbour ballistic deposition on $\mathbb Z$ from a flat surface, there are constants $c,C\in(0,\infty)$ such that for every $t\ge1$ and $r\ge0$,
--
--   $$
--   P\big(|\xi_t(0)-E\xi_t(0)|\ge r\big)\le C\exp\Big\{-c\,\frac{r^2}{t+r}\Big\}.
--   $$
--
--   This exponential concentration inequality implies the diffusive variance bound $\operatorname{Var}\xi_t(0)\le Ct$.
-- source:
--   T. Sudijono, A Linear Variance Bound for Ballistic Deposition (2026), https://arxiv.org/abs/2609.24056, Theorem 1.1, inequality (2), p. 2 (case d = 1)

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem sudijono_thm_1_1_concentration {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ r : ℝ, 0 ≤ r →
      P.real {ω | r ≤ |bdHeightReal τ t 0 ω - ∫ ω', bdHeightReal τ t 0 ω' ∂P|} ≤
        C * Real.exp (-c * r ^ 2 / (t + r)) := by sorry

end KPZBallistic
