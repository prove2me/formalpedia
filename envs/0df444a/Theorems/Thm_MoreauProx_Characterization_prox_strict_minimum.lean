-- Prove2me | Theorems.Thm_MoreauProx_Characterization_prox_strict_minimum
-- name    : MoreauProx.Characterization.prox_strict_minimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:17:53.86096+00:00
-- url     : https://prove2.me/theorems/cbf7a724-5a8c-46d7-a58c-99196683b8a8
-- title:
--   Proposition 3.a — the proximal objective ½‖u − z‖² + f(u) has a strict minimum
-- statement:
--   Let $H$ be a real Hilbert space and $f \in \Gamma_0(H)$. For every $z \in H$ the function
--   $$
--   \Phi(u) = \tfrac12 \|u - z\|^2 + f(u)
--   $$
--   has a strict minimum: there is $x \in H$ such that $\Phi(x) < \Phi(u)$ for every $u \ne x$.
--
--   This is what makes the proximal point $\operatorname{prox}_f z$ well defined for every $f \in \Gamma_0(H)$ and every $z$: the strict minimum gives both existence and uniqueness of the minimizer.
--
--   **Formalization Note** Values are computed in `EReal`; the strict inequality is required against every other point, which is stronger than the existence of a minimizer.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 278, Proposition 3.a

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem prox_strict_minimum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (z : H) :
    ∃ x : H, ∀ u : H, u ≠ x →
      ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + f x < ((‖u - z‖ ^ 2 / 2 : ℝ) : EReal) + f u := by sorry

end MoreauProx.Characterization
