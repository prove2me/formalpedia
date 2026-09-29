-- Prove2me | Theorems.Thm_MoreauProx_Characterization_prox_map_characterization
-- name    : MoreauProx.Characterization.prox_map_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:22:25.635521+00:00
-- url     : https://prove2.me/theorems/947249cd-274d-426a-b99c-19e17eacd640
-- title:
--   Corollary 10.c — p is a prox map iff it is nonexpansive and p(z) ∈ ∂φ(z) for a convex φ
-- statement:
--   Let $H$ be a real Hilbert space and $p : H \to H$ a (single-valued, everywhere defined) map. Then $p$ is a prox map, i.e. $p = \operatorname{prox}_g$ for some $g \in \Gamma_0(H)$, if and only if both of the following hold:
--
--   1. $p$ contracts distances: $\|p(z) - p(z')\| \le \|z - z'\|$ for all $z, z' \in H$;
--   2. there is a convex function $\varphi$ such that, for every $z \in H$,
--   $$
--   p(z) \in \partial\varphi(z),
--   $$
--   that is, $\varphi(z) + (u - z \mid p(z)) \le \varphi(u)$ for all $u \in H$.
--
--   Prox maps are thus exactly the nonexpansive maps that select a subgradient of some convex function at every point. No differentiability, lower semicontinuity or membership in $\Gamma_0(H)$ is assumed of $\varphi$.
--
--   **Formalization Note** The contraction condition is the paper's definition (§10.a) applied to the singleton-valued map $z \mapsto \{p(z)\}$. The paper allows $\varphi$ to take values in $]-\infty, +\infty]$; we state the result with $\varphi : H \to \mathbb{R}$ convex (Mathlib's `ConvexOn`). This is equivalent: a subgradient at $z$ requires $\varphi(z)$ finite, so a $\varphi$ with $p(z) \in \partial\varphi(z)$ for every $z$ is finite everywhere, and the $\varphi$ produced by the forward direction (the primitive of $p$) is real-valued. Subgradients are in the affine-minorant form (the paper's gloss of (2.4), p. 277), which is meaningful for $\varphi$ outside $\Gamma_0(H)$.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 292, Corollaire 10.c, (10.2)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox
open scoped InnerProductSpace

namespace MoreauProx.Characterization

theorem prox_map_characterization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (p : H → H) :
    IsProxMap p ↔
      (ContractsDistances (fun z => ({p z} : Set H)) ∧
        ∃ φ : H → ℝ, ConvexOn ℝ Set.univ φ ∧
          ∀ z : H, p z ∈ subgrad (fun u => ((φ u : ℝ) : EReal)) z) := by sorry

end MoreauProx.Characterization
