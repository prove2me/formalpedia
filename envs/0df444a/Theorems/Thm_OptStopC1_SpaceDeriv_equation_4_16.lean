-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_equation_4_16
-- name    : OptStopC1.SpaceDeriv.equation_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:16.050687+00:00
-- url     : https://prove2.me/theorems/eb56ad2d-161d-48ac-8323-e837bf26b31c
-- title:
--   Equation (4.16) — lower limit of the value derivative
-- statement:
--   Assume Theorem 8's well-posed infinite-horizon stopping problem, conditions (4.1)–(4.3), a C¹ spatial flow, and all four local integrability bounds at $z\in\partial C$. At $z$, require $\partial_iX^{j,z}_{0+}=\delta_{ij}$ and either strong Feller plus probabilistic regularity for $D$, or probabilistic regularity for $D^\circ$.
--
--   For every sequence $x_n\in C$ with $x_n\to z$ and each coordinate $i$,
--
--   $$\liminf_{n\to\infty}\partial_iV(x_n)\ge\partial_iG(z).$$
--
--   This is the lower half of the boundary derivative comparison for the general discount function.
--
--   **Formalization Note** The extended lower-limit inequality is written as: for every $c<\partial_iG(z)$, eventually $c<\partial_iV(x_n)$. This avoids the default value of a real-valued `liminf` on an unbounded sequence.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 13, §4.1, equation (4.16)

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem equation_4_16
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (p : StoppingProblem d Ω P 𝔽)
    (hcommon : Theorem8Common p)
    (z : State d) (hz : z ∈ stoppingBoundary p)
    (hzreg : BoundaryHypotheses p z)
    (xs : ℕ → State d) (hxs : ∀ n, xs n ∈ continuationSet p)
    (hconv : Tendsto xs atTop (𝓝 z)) (i : Fin d) :
    ∀ c : ℝ, c < rewardPartial p i z →
      ∀ᶠ n in atTop,
        c < (fderiv ℝ (value p) (xs n)) (EuclideanSpace.single i (1 : ℝ)) := by sorry
end OptStopC1.SpaceDeriv
