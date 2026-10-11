-- Prove2me | Theorems.Thm_KPZBallistic_sudijono_thm_1_1_variance
-- name    : KPZBallistic.sudijono_thm_1_1_variance
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:32:16.788481+00:00
-- url     : https://prove2.me/theorems/73277959-15f9-4f3a-9d90-b87570271c9b
-- title:
--   Sudijono Thm. 1.1 (3): $\mathrm{Var}\,\xi_t(0)\le Ct$
-- statement:
--   In one-dimensional nearest-neighbour ballistic deposition on $\mathbb Z$ from a flat surface, there is a constant $C\in(0,\infty)$ such that
--
--   $$
--   \operatorname{Var}\xi_t(0)\le C\,t\qquad\text{for all } t\ge1.
--   $$
--
--   This is the best known upper bound on the height fluctuations; the KPZ prediction is $\operatorname{Var}\xi_t(0)\asymp t^{2/3}$.
-- source:
--   T. Sudijono, A Linear Variance Bound for Ballistic Deposition (2026), https://arxiv.org/abs/2609.24056, Theorem 1.1, inequality (3), p. 2 (case d = 1)

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem sudijono_thm_1_1_variance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → variance (bdHeightReal τ t 0) P ≤ C * t := by sorry

end KPZBallistic
