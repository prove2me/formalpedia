-- Prove2me | Theorems.Thm_GeomDL_Blueprint_pointwise_comp_equivariant
-- name    : GeomDL.Blueprint.pointwise_comp_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:15.348643+00:00
-- url     : https://prove2.me/theorems/8ab5f179-b94e-4e07-bb9a-83d6bea6e26c
-- title:
--   §3.5, p. 27 — an element-wise nonlinearity after an equivariant map is equivariant, U = σ ∘ B
-- statement:
--   Let a group $\mathfrak G$ act on a domain $\Omega$ and on signals by $(\mathfrak g . x)(u) = x(\mathfrak g^{-1}u)$. Let $B : X(\Omega, C) \to X(\Omega, C')$ be $\mathfrak G$-equivariant, $B(\mathfrak g . x) = \mathfrak g . B(x)$, and let $\sigma : C' \to C''$ be an arbitrary map, applied element-wise as $(\boldsymbol\sigma(x))(u) = \sigma(x(u))$. Then
--   $$U := \boldsymbol\sigma \circ B : X(\Omega, C) \to X(\Omega, C''), \qquad U(\mathfrak g . x) = \mathfrak g . U(x)$$
--   for all $\mathfrak g \in \mathfrak G$ and $x \in X(\Omega, C)$.
--
--   Nonlinearities applied element-wise preserve equivariance; this is how the blueprint gets expressive equivariant layers.
--
--   **Formalization Note** $C$, $C'$, $C''$ are arbitrary types; no linear structure is used.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §3.5, p. 27, "Indeed, if B : X(Ω, C) → X(Ω, C′) is G-equivariant ..."

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

namespace GeomDL.Blueprint

/-- Bronstein et al., §3.5, p. 27: if `B : X(Ω, C) → X(Ω, C′)` is `G`-equivariant and
`σ : C′ → C″` is an arbitrary (non-linear) map, then `U := σ ∘ B : X(Ω, C) → X(Ω, C″)` is
`G`-equivariant, where `σ` acts element-wise, `(σ(x))(u) := σ(x(u))`. -/
theorem pointwise_comp_equivariant {G Ω C C' C'' : Type*} [Group G] [MulAction G Ω]
    (B : (Ω → C) → (Ω → C')) (σ : C' → C'') (hB : IsEquivariant (G := G) B) :
    IsEquivariant (G := G) (pointwise (Ω := Ω) σ ∘ B) := by sorry

end GeomDL.Blueprint
