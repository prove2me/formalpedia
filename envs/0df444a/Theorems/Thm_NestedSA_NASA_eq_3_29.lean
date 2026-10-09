-- Prove2me | Theorems.Thm_NestedSA_NASA_eq_3_29
-- name    : NestedSA.NASA.eq_3_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:39:51.842188+00:00
-- url     : https://prove2.me/theorems/ee337777-76cf-46e6-ada3-94bc5c433500
-- title:
--   (3.29) — V(x,z) ≤ max(1,β²)‖d‖² + ‖z − ∇F(x)‖²
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, $x\in X$, $z\in\mathbb R^n$, $\beta>0$, $F=f\circ g$, and $d=\bar y(x,z,\beta)-x$. Then the optimality measure (2.10) satisfies
--   $$V(x,z)\le\max(1,\beta^2)\,\|d\|^2+\|z-\nabla F(x)\|^2.$$
--
--   Applied at the iterates, this reduces a bound on $V(x^k,z^k)$ to bounds on the step $\|d^k\|$ and on the gradient-tracking error $\|z^k-\nabla F(x^k)\|$.
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, §3, (3.29), p. 13

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic

namespace NestedSA.NASA

/-- (3.29) (p. 13): for a closed convex `X` with Euclidean projection `P`, every `x ∈ X`, every `z` and every
`β > 0`, `V(x, z) ≤ max(1, β²) ‖d‖² + ‖z − ∇F(x)‖²` with `d = ȳ(x, z, β) − x` and `F = f ∘ g`. -/
theorem eq_3_29 {n m : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β) :
    V P f g x z ≤ max 1 (β ^ 2) * ‖ybar P x z β - x‖ ^ 2 + ‖z - gradF f g x‖ ^ 2 := by sorry

end NestedSA.NASA
