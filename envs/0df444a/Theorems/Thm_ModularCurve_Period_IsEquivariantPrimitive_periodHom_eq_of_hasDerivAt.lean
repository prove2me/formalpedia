-- Prove2me | Theorems.Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt
-- name    : ModularCurve.Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/5b3899e9-05cf-5d4a-a94c-5e32bc1065ab
-- title:
--   Equal derivatives give equal period homomorphisms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb{Z})$ and let $F, G, f \colon \mathbb{H} \to \mathbb{C}$ be functions on the upper half-plane. Assume that $F$ is an equivariant primitive for $\Gamma$, in the sense that for every $\gamma \in \Gamma$ there is a constant $c \in \mathbb{C}$ with $F(\gamma \cdot z) - F(z) = c$ for all $z \in \mathbb{H}$, and likewise for $G$. Assume further that $f$ is a common derivative of the two: for every $\tau \in \mathbb{H}$ the function $F \circ \mathrm{ofComplex} \colon \mathbb{C} \to \mathbb{C}$, obtained by extending $F$ along the canonical section `UpperHalfPlane.ofComplex`, has complex derivative $f(\tau)$ at the point $\tau$, and the same holds for $G \circ \mathrm{ofComplex}$ with the same value $f(\tau)$. The conclusion is that the two associated period homomorphisms coincide, i.e. the additive group homomorphisms $\mathrm{Additive}\,\Gamma \to \mathbb{C}$ sending $\gamma$ to $F(\gamma \cdot i) - F(i)$ and to $G(\gamma \cdot i) - G(i)$ respectively are equal; in particular $F(\gamma \cdot i) - F(i) = G(\gamma \cdot i) - G(i)$ for every $\gamma \in \Gamma$.
--
--   This is the well-definedness statement for the period character attached to a weight-two form: the period homomorphism depends only on the derivative $f$, not on the choice of primitive. It is used when comparing primitives built in different ways, for instance in the proofs that the period homomorphism of a nonzero cusp form is nonzero and in the computations of the period map on $\Gamma_H$-level structures and its compatibility with the Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt.lean

import Definitions.Def_ModularCurve_PeriodMapBundled

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt {Γ : Subgroup SL(2, ℤ)}
    {F G : UpperHalfPlane → ℂ} {f : UpperHalfPlane → ℂ}
    (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F) (hG : ModularCurve.Period.IsEquivariantPrimitive Γ G)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ)
    (hGf : ∀ τ : UpperHalfPlane, HasDerivAt (G ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hF.periodHom = hG.periodHom := by sorry
