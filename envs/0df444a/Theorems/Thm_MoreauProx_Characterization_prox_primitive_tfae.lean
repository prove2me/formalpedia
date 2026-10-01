-- Prove2me | Theorems.Thm_MoreauProx_Characterization_prox_primitive_tfae
-- name    : MoreauProx.Characterization.prox_primitive_tfae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:21:25.571842+00:00
-- url     : https://prove2.me/theorems/ae599d11-adc6-4563-af33-dbeeb00c26e3
-- title:
--   Proposition 9.b — φ is less convex than 𝒬 ⟺ its dual is more convex than 𝒬 ⟺ φ is a prox primitive
-- statement:
--   Let $H$ be a real Hilbert space, $\mathcal{Q}(z) = \tfrac12\|z\|^2$, and $\varphi : H \to [-\infty, +\infty]$. The following three properties are equivalent:
--
--   1. $\varphi \in \Gamma_0(H)$ and $\varphi$ is less convex than $\mathcal{Q}$;
--   2. $\varphi \in \Gamma_0(H)$ and the dual function of $\varphi$ is more convex than $\mathcal{Q}$;
--   3. $\varphi$ is the primitive of a prox map: there is $g \in \Gamma_0(H)$ such that, with $f$ the dual function of $g$,
--   $$
--   \varphi(z) = \tfrac12 \|\operatorname{prox}_g z\|^2 + f(\operatorname{prox}_f z) \quad \text{for all } z \in H.
--   $$
--
--   The proposition describes the primitives of prox maps intrinsically, without reference to $g$. Together with Proposition 10.b it reduces the characterization of prox maps (Corollary 10.c) to a statement about subgradients.
--
--   **Formalization Note** The equivalence is stated as `List.TFAE`. Property 3 does not itself assume $\varphi \in \Gamma_0(H)$, as in the paper; "less/more convex than $\mathcal{Q}$" uses an auxiliary convex function with values in $]-\infty, +\infty]$ (Définition 9.b).
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 288, Définition 9.b; p. 289, Proposition 9.b

import Mathlib
import Definitions.Def_MoreauProx_Characterization_ConvexityVsQ
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem prox_primitive_tfae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ : H → EReal) :
    List.TFAE
      [GammaZero φ ∧ LessConvexThanQ φ,
       GammaZero φ ∧ MoreConvexThanQ (conj φ),
       IsProxPrimitive φ] := by sorry

end MoreauProx.Characterization
