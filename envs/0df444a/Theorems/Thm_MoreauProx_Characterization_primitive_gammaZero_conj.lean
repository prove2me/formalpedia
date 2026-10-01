-- Prove2me | Theorems.Thm_MoreauProx_Characterization_primitive_gammaZero_conj
-- name    : MoreauProx.Characterization.primitive_gammaZero_conj
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:20:12.234822+00:00
-- url     : https://prove2.me/theorems/84a6f1be-c251-4077-9b19-9b0e44bd7adf
-- title:
--   Proposition 7.b — the primitive φ of prox_g lies in Γ₀(H) and its dual is g + ½‖·‖²
-- statement:
--   Let $H$ be a real Hilbert space, $f \in \Gamma_0(H)$ and $g$ its dual function. Let $\varphi$ be the primitive of $\operatorname{prox}_g$,
--   $$
--   \varphi(z) = \tfrac12 \|\operatorname{prox}_g z\|^2 + f(\operatorname{prox}_f z).
--   $$
--   Then $\varphi \in \Gamma_0(H)$, and the dual function of $\varphi$ is
--   $$
--   \theta(y) = g(y) + \tfrac12 \|y\|^2 .
--   $$
--
--   Since $\varphi(z) = \inf_u \big[\tfrac12\|u - z\|^2 + f(u)\big]$ (Remark 7.c), this identifies $\varphi$ as the inf-convolution of $f$ with $\tfrac12\|\cdot\|^2$ and computes its dual; it is used for Propositions 9.b and 10.b.
--
--   **Formalization Note** $\varphi$ is real-valued and is viewed as an `EReal`-valued function to apply the definitions of $\Gamma_0(H)$ and of the dual function; the identity of duals is an equality of `EReal`-valued functions on $H$ (where $g$ may take the value $+\infty$).
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 284, Proposition 7.b

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem primitive_gammaZero_conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) :
    GammaZero (fun z => ((primitive f g z : ℝ) : EReal)) ∧
      conj (fun z => ((primitive f g z : ℝ) : EReal)) =
        fun y => g y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal) := by sorry

end MoreauProx.Characterization
