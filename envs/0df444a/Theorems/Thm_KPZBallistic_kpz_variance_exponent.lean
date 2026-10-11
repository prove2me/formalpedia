-- Prove2me | Theorems.Thm_KPZBallistic_kpz_variance_exponent
-- name    : KPZBallistic.kpz_variance_exponent
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:32:45.869332+00:00
-- url     : https://prove2.me/theorems/c45bfcf3-63c8-4f33-a430-65efd153a000
-- title:
--   KPZ fluctuation exponent for ballistic deposition: $\mathrm{Var}\,\xi_t(0)\asymp t^{2/3}$
-- statement:
--   Let $\xi_t(0)$ be the height of column $0$ at time $t$ in one-dimensional (nearest-neighbour) ballistic deposition on $\mathbb Z$, started from a flat surface and driven by independent rate-one Poisson clocks. There are constants $0<c\le C<\infty$ and $T$ such that
--
--   $$
--   c\,t^{2/3}\le \operatorname{Var}\xi_t(0)\le C\,t^{2/3}\qquad\text{for all } t\ge T.
--   $$
--
--   This is the KPZ prediction that the column height fluctuates around its mean on the scale $t^{1/3}$; it is open. The best known bounds are $\operatorname{Var}\xi_t(0)\gtrsim\log t$ (Penrose 2008) and $\operatorname{Var}\xi_t(0)\lesssim t$ (Sudijono 2026).
--
--   **Formalization Note** Mathlib's `variance` is $0$ for variables that are not square-integrable, so the lower bound also forces square-integrability.
-- source:
--   Open Problem Garden, 'KPZ Universality Conjecture' (posted by T. Kojar, 2020), http://www.openproblemgarden.org/op/kpz_universality_conjecture; I. Corwin, The Kardar-Parisi-Zhang equation and universality class, Random Matrices Theory Appl. 1 (2012), https://arxiv.org/abs/1106.1596, Section 1.1.1, p. 3 ('in time t the column height will fluctuate around its mean like t^{1/3} ... This prediction has not been proved'); T. Sudijono, A Linear Variance Bound for Ballistic Deposition (2026), https://arxiv.org/abs/2609.24056, Section 1, p. 2 ('Var f(t,0) is expected to scale as t^{2/3} when d = 1')

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem kpz_variance_exponent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ ∀ t ≥ T,
      c * t ^ ((2 : ℝ) / 3) ≤ variance (bdHeightReal τ t 0) P ∧
      variance (bdHeightReal τ t 0) P ≤ C * t ^ ((2 : ℝ) / 3) := by sorry

end KPZBallistic
