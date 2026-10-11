-- Prove2me | Theorems.Thm_KPZBallistic_seppalainen_strong_law
-- name    : KPZBallistic.seppalainen_strong_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:30:53.737158+00:00
-- url     : https://prove2.me/theorems/a26c9c46-7d5a-4414-949f-b5dd9182fe08
-- title:
--   Seppäläinen: $\xi_t(0)/t\to\rho_1$ almost surely
-- statement:
--   In one-dimensional nearest-neighbour ballistic deposition on $\mathbb Z$ from a flat surface, there is a constant $\rho_1\in(0,\infty)$ with $E[\xi_t(0)]/t\to\rho_1$ and
--
--   $$
--   \frac{\xi_t(0)}{t}\to\rho_1\qquad\text{almost surely as } t\to\infty.
--   $$
--
--   This is the strong law of large numbers for the height of a column; the limit is the same constant as in the $L^p$ law of large numbers.
-- source:
--   M. D. Penrose, Growth and roughness of the interface for ballistic deposition, J. Stat. Phys. 131 (2008), https://arxiv.org/abs/math/0608540, remark after Theorem 2.1, p. 5 ('In the special case of the NN model, it can be deduced from Theorem 1 of Seppalainen [19] that (2.11) holds with almost sure convergence'); T. Seppalainen, Strong law of large numbers for the interface in ballistic deposition, Ann. Inst. H. Poincare Probab. Statist. 36 (2000), https://arxiv.org/abs/math/9906193, Theorem 1

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem seppalainen_strong_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun t : ℝ => (∫ ω, bdHeightReal τ t 0 ω ∂P) / t) atTop (𝓝 ρ) ∧
      ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => bdHeightReal τ t 0 ω / t) atTop (𝓝 ρ) := by sorry

end KPZBallistic
