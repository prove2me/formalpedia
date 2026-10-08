-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_theorem_8
-- name    : OptStopC1.SpaceDeriv.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:23.186876+00:00
-- url     : https://prove2.me/theorems/0e5327cc-d0d2-4b23-8fa4-70ac73d9c2ed
-- title:
--   Theorem 8 (4.8) — pointwise C¹ fit at a boundary point
-- statement:
--   Assume Theorem 8's well-posed infinite-horizon stopping problem, conditions (4.1)–(4.3), a C¹ spatial flow, and all four local integrability bounds at $z\in\partial C$. At $z$, require $\partial_iX^{j,z}_{0+}=\delta_{ij}$ and either strong Feller plus probabilistic regularity for $D$, or probabilistic regularity for $D^\circ$.
--
--   The value function is differentiable at $z$ with the same derivative as $G$, and its derivative from continuation points tends to that derivative:
--
--   $$D V(z)=D G(z),\qquad \lim_{C\ni x\to z}D V(x)=D G(z).$$
--
--   In particular, $\partial_iV(z)=\partial_iG(z)$ for every coordinate. This is the pointwise conclusion used to establish global C¹ regularity.
--
--   **Formalization Note** The pointwise claim uses Fréchet differentiability and a derivative limit along $C$. `ContDiffAt` would assert differentiability on a whole neighborhood and would be stronger than the paper's pointwise claim.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 11–12, Theorem 8, equation (4.8)

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem theorem_8
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (p : StoppingProblem d Ω P 𝔽)
    (hcommon : Theorem8Common p)
    (z : State d) (hz : z ∈ stoppingBoundary p)
    (hzreg : BoundaryHypotheses p z) :
    HasFDerivAt (value p) (fderiv ℝ p.G z) z ∧
    Tendsto (fderiv ℝ (value p)) (𝓝[continuationSet p] z)
      (𝓝 (fderiv ℝ p.G z)) := by sorry
end OptStopC1.SpaceDeriv
