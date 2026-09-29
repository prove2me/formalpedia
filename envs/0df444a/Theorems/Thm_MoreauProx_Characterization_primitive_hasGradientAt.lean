-- Prove2me | Theorems.Thm_MoreauProx_Characterization_primitive_hasGradientAt
-- name    : MoreauProx.Characterization.primitive_hasGradientAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:20:43.075904+00:00
-- url     : https://prove2.me/theorems/2c2146e1-8ba9-485d-9d33-b36a9ec55116
-- title:
--   Proposition 7.d — the primitive φ is Fréchet differentiable with gradient prox_g z
-- statement:
--   Let $H$ be a real Hilbert space, $f \in \Gamma_0(H)$ and $g$ its dual function, and let $\varphi(z) = \tfrac12 \|\operatorname{prox}_g z\|^2 + f(\operatorname{prox}_f z)$ be the primitive of $\operatorname{prox}_g$. At every point $z \in H$, $\varphi$ is Fréchet differentiable and its gradient is
--   $$
--   \nabla \varphi(z) = \operatorname{prox}_g z .
--   $$
--
--   This justifies the name "primitive": $\operatorname{prox}_g$ is the gradient of the convex function $\varphi$. It is the key input for the necessity half of Corollary 10.c.
--
--   **Formalization Note** The gradient is Mathlib's `HasGradientAt`, which is Fréchet differentiability with derivative $h \mapsto (\operatorname{prox}_g z \mid h)$. The gradient is $\operatorname{prox}_g z$, not $\operatorname{prox}_f z$.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 286, Proposition 7.d

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem primitive_hasGradientAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (z : H) :
    HasGradientAt (primitive f g) (prox g z) z := by sorry

end MoreauProx.Characterization
