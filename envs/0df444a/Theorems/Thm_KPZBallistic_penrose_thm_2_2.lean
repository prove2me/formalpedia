-- Prove2me | Theorems.Thm_KPZBallistic_penrose_thm_2_2
-- name    : KPZBallistic.penrose_thm_2_2
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:31:20.271293+00:00
-- url     : https://prove2.me/theorems/e59a551c-83c6-41d1-a633-536ca47a878e
-- title:
--   Penrose Thm. 2.2: $\liminf \mathrm{Var}\,\xi_t(0)/\log t>0$
-- statement:
--   In one-dimensional nearest-neighbour ballistic deposition on $\mathbb Z$ from a flat surface, let $w^2(t)=\operatorname{Var}\xi_t(0)$. Then
--
--   $$
--   \liminf_{t\to\infty}w^2(t)>0\qquad\text{and}\qquad\liminf_{t\to\infty}\frac{w^2(t)}{\log t}>0.
--   $$
--
--   This is the only known lower bound on the height fluctuations of ballistic deposition; the KPZ prediction is $w^2(t)\asymp t^{2/3}$.
--
--   **Formalization Note** Each $\liminf$ statement is encoded in the equivalent form: there are $c>0$ and $T$ with $c\le w^2(t)$, respectively $c\log t\le w^2(t)$, for all $t\ge T$.
-- source:
--   M. D. Penrose, Growth and roughness of the interface for ballistic deposition, J. Stat. Phys. 131 (2008), https://arxiv.org/abs/math/0608540, Section 2, Theorem 2.2, eqs. (2.12)-(2.13), p. 6 (case d = 1, N a lattice interval: nearest-neighbour model)

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem penrose_thm_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    (∃ c T : ℝ, 0 < c ∧ ∀ t ≥ T, c ≤ variance (bdHeightReal τ t 0) P) ∧
    (∃ c T : ℝ, 0 < c ∧ ∀ t ≥ T, c * Real.log t ≤ variance (bdHeightReal τ t 0) P) := by sorry

end KPZBallistic
