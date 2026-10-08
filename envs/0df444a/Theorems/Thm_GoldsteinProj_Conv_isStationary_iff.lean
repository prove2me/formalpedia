-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_isStationary_iff
-- name    : GoldsteinProj.Conv.isStationary_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:23:45.105688+00:00
-- url     : https://prove2.me/theorems/e2de6808-4164-49fe-a731-a62dc5a1ca20
-- title:
--   p. 709 — z ∈ C is stationary iff the linear functional f′(z, ·) attains its minimum on C at z
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ convex, $P$ the projection onto $C$, $f : H \to \mathbb R$ convex on $C$, and $z \in C$ where $f$ is Fréchet differentiable. Write $f'(z, \cdot)$ for the Fréchet derivative of $f$ at $z$ and $\nabla f(z)$ for its Riesz representative. Then $z$ is stationary, i.e. $P(z - \rho \nabla f(z)) = z$ for every $\rho > 0$, if and only if
--   $$f'(z, z) \le f'(z, y) \qquad \text{for all } y \in C.$$
--
--   The second condition is the first-order optimality condition of minimizing $f$ over $C$; for convex $f$ it characterizes minimizers.
--
--   **Formalization Note** The convexity hypothesis retains the paper's "when $f$ is convex" qualifier. Differentiability at $z$ ensures that Lean's total `fderiv` and `gradient` denote the derivative and gradient the paper uses.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, last sentence of the paragraph before the THEOREM

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 709: when `f` is convex and differentiable at `z ∈ C`, the point is
stationary (`P(z - ρ∇f(z)) = z` for all `ρ > 0`) if and only if the linear functional
`f′(z, ·)` attains its minimum over `C` at `z`. -/
theorem isStationary_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hfcvx : ConvexOn ℝ C f) (z : H) (hz : z ∈ C)
    (hfdiff : DifferentiableAt ℝ f z) :
    IsStationary f C P z ↔ ∀ y ∈ C, fderiv ℝ f z z ≤ fderiv ℝ f z y := by sorry

end GoldsteinProj.Conv
