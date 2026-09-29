-- Prove2me | Theorems.Thm_MoreauProx_Characterization_prox_primitive_iff_subgrad_contracts
-- name    : MoreauProx.Characterization.prox_primitive_iff_subgrad_contracts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:21:55.551795+00:00
-- url     : https://prove2.me/theorems/4edd03cb-8b91-4dcd-8c81-51962af8a752
-- title:
--   Proposition 10.b — φ ∈ Γ₀(H) with ∂φ contracting distances ⟺ the three properties of 9.b
-- statement:
--   Let $H$ be a real Hilbert space and $\varphi : H \to [-\infty, +\infty]$. Consider the property
--
--   (IV) $\varphi \in \Gamma_0(H)$ and the (a priori multivalued) map $z \mapsto \partial\varphi(z)$ contracts distances:
--   $$
--   x \in \partial\varphi(z),\ x' \in \partial\varphi(z') \ \Longrightarrow\ \|x - x'\| \le \|z - z'\|.
--   $$
--
--   Then (IV) is equivalent to each of the three properties of Proposition 9.b:
--
--   1. $\varphi \in \Gamma_0(H)$ and $\varphi$ is less convex than $\mathcal{Q}(z) = \tfrac12\|z\|^2$;
--   2. $\varphi \in \Gamma_0(H)$ and the dual function of $\varphi$ is more convex than $\mathcal{Q}$;
--   3. $\varphi$ is the primitive of $\operatorname{prox}_g$ for some $g \in \Gamma_0(H)$.
--
--   This is the step from the convexity comparisons of Section 9 to a metric condition on subgradients, on which the characterization of prox maps (Corollary 10.c) rests.
--
--   **Formalization Note** The contraction condition is the paper's definition for multivalued maps (§10.a); it places no condition at points where $\partial\varphi(z)$ is empty. Subgradients are in the affine-minorant form, which agrees with the paper's definition on $\Gamma_0(H)$.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 291, §10.a and Proposition 10.b

import Mathlib
import Definitions.Def_MoreauProx_Characterization_ConvexityVsQ
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem prox_primitive_iff_subgrad_contracts {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : H → EReal) :
    ((GammaZero φ ∧ ContractsDistances (subgrad φ)) ↔ (GammaZero φ ∧ LessConvexThanQ φ)) ∧
    ((GammaZero φ ∧ ContractsDistances (subgrad φ)) ↔
      (GammaZero φ ∧ MoreConvexThanQ (conj φ))) ∧
    ((GammaZero φ ∧ ContractsDistances (subgrad φ)) ↔ IsProxPrimitive φ) := by sorry

end MoreauProx.Characterization
