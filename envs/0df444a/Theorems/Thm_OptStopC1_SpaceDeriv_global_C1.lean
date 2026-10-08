-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_global_C1
-- name    : OptStopC1.SpaceDeriv.global_C1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:20.425814+00:00
-- url     : https://prove2.me/theorems/d642e837-3c0c-4f0f-89e6-0bd3017af1ba
-- title:
--   Theorem 8 — global continuous differentiability of the value function
-- statement:
--   Let $V$ be the value function of the well-posed infinite-horizon optimal stopping problem (2.1). Assume $V$ is continuous and C¹ on its continuation set $C$, $G$ is C¹ on $\mathbb R^d$, $H$ and $\lambda$ share a positive Lipschitz constant, and the standard Markov process admits a C¹ spatial flow. Suppose that at every point $z\in\partial C$ the bounds (4.4)–(4.7), the initial flow derivative condition, and one of Theorem 8's two boundary regularity alternatives hold. Then
--
--   $$V\in C^1(\mathbb R^d).$$
--
--   The theorem promotes interior regularity and regularity at every optimal stopping boundary point to global continuous differentiability.
--
--   **Formalization Note** The model allows any $d\ge1$, a common right-continuous filtration and finite stopping times, including nonconstant discount and càdlàg flows. The second boundary branch is probabilistic regularity for $D^\circ$ under the standing strong Markov model.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 11–12, Theorem 8, final sentence

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem global_C1
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (p : StoppingProblem d Ω P 𝔽)
    (hcommon : Theorem8Common p)
    (hall : ∀ z ∈ stoppingBoundary p, BoundaryHypotheses p z) :
    ContDiff ℝ 1 (value p) := by sorry
end OptStopC1.SpaceDeriv
