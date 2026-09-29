-- Prove2me | Theorems.Thm_MoreauProx_Decomposition_prox_strict_minimum
-- name    : MoreauProx.Decomposition.prox_strict_minimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:12:32.598683+00:00
-- url     : https://prove2.me/theorems/7666e19a-4d6f-4930-8735-8c96a1af39b6
-- title:
--   Proposition 3.a — the proximal objective ½‖u − z‖² + f(u) has a strict minimum
-- statement:
--   Let $H$ be a real Hilbert space, $f \in \Gamma_0(H)$ and $z \in H$. Then the function
--   $$ \Phi(u) = \tfrac12 \|u - z\|^2 + f(u), \qquad u \in H, $$
--   with values in $]-\infty,+\infty]$, has a strict minimum: there is a point $x \in H$ such that $\Phi(x) < \Phi(u)$ for every $u \ne x$.
--
--   The minimizer is therefore unique; Moreau denotes it $\mathrm{prox}_f z$, the *proximal point* of $z$ relative to $f$ (3.b). For $f$ the indicator function of a nonempty closed convex set $C$, it is the nearest-point projection onto $C$.
--
--   **Formalization Note** "Strict minimum" is stated literally, as strict inequality at every other point, which gives both existence and uniqueness of the minimizer. The sum is computed in `EReal`.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 278, Proposition 3.a

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

/-- Moreau 1965, Proposition 3.a, p. 278: for `f ∈ Γ₀(H)` and every `z ∈ H`, the function
`Φ(u) = ½‖u − z‖² + f(u)` has a strict minimum: a point `x` with `Φ(x) < Φ(u)` for all `u ≠ x`. -/
theorem prox_strict_minimum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (z : H) :
    ∃ x : H, ∀ u : H, u ≠ x → proxObjective f z x < proxObjective f z u := by sorry

end MoreauProx.Decomposition
