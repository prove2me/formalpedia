-- Prove2me | Theorems.Thm_NonlinSSD_Optimality_weak_duality
-- name    : NonlinSSD.Optimality.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:00:41.505135+00:00
-- url     : https://prove2.me/theorems/a9d0bb7f-59d6-4a2e-9a2b-4b07374c12f5
-- title:
--   p. 10, proof of Theorem 2 — weak duality at feasible points
-- statement:
--   For any feasible pair $(z,X)$ of (11)–(14), utilities $u_i\in\mathcal U_1([a_i,b_i])$, and essentially bounded multipliers $\theta_i\ge0$ almost surely,
--   $$\mathbb E[H(z)]\le L(z,X,u,\theta).$$
--
--   This inequality is the comparison used in the sufficiency direction of Theorem 2.
--
--   **Formalization Note** Feasibility includes integrability of every $X_i$, interval restricted dominance, and $X_i\le G_i(z)$ almost surely. Essential boundedness and almost sure nonnegativity of $\theta$ make the product terms integrable and nonnegative in expectation.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 10, proof of Theorem 2 (converse)

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.Optimality

open MeasureTheory

/-- p. 10, proof of Theorem 2 (converse): at a feasible point the Lagrangian
dominates the primal objective for every dual-feasible pair. -/
theorem weak_duality
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (pr : Problem Ω 𝒵 P m) (z : 𝒵) (X : Fin m → Ω → ℝ)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ)
    (hfeas : pr.Feasible z X)
    (hu : pr.UtilityAdmissible u)
    (hθ : pr.MultiplierAdmissible θ) :
    (∫ ω, pr.H z ω ∂P) ≤ pr.L z X u θ := by sorry

end NonlinSSD.Optimality
