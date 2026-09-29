-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
-- name    : MvPolynomial.CrossingQuotient.Resolution.exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/35295495-9959-5551-9344-6465e987f9f2
-- title:
--   Fibre-maximal points over the vertex are exceptional-line generic points
-- statement:
--   Let $W$ be a commutative ring, $t \in W$, $e$ a natural number, and $\mathfrak p$ a maximal ideal of $W$ with $t \in \mathfrak p$, and assume $1 \le e$. Let $o$ be a point of the scheme `Resolution t e`, the colimit of the gluing diagram `glueDiagram t e` whose objects are the $e$ charts over the crossing $\operatorname{Spec}\bigl(W[X_0,X_1]/(X_0X_1 - t^e)\bigr)$. Assume two things about $o$: first, that its image under the canonical morphism `toCrossing t e` to $\operatorname{Spec}\bigl(W[X_0,X_1]/(X_0X_1-t^e)\bigr)$ is the vertex point `vertexPt t e 𝔭 ht he`, the prime `originIdeal` attached to $\mathfrak p$ and $t^e$; second, a maximality condition in the fibre over $t$: every point $o'$ of `Resolution t e` which specialises to $o$ (i.e. $o' \rightsquigarrow o$) and whose image under the structure morphism `toSpec t e` to $\operatorname{Spec} W$ is a prime of $W$ containing $t$ must equal $o$. The conclusion is that there exists $k \in \mathrm{Fin}\,(e-1)$ with $o =$ `lineUGen t e 𝔭 ht ⟨k, _⟩`, the image under the $k$-th chart inclusion `ι t e k` of the prime $\ker(\mathrm{lineUHom}\ t\ \mathfrak p\ ht)$ of the chart ring $W[X_0,X_1]/(X_0X_1-t)$, the index $k$ being regarded as an element of $\mathrm{Fin}\,e$.
--
--   This is the fibre-topological classification of points of the resolution of the crossing $uv = t^e$ lying over the vertex: the ones that are maximal in the fibre over $t$ are exactly the generic points of the $e-1$ exceptional lines. It is used in the codimension computations [`V3Asm.codim`](thm.html#V3Asm.codim) and [`V3AsmLevel.codim`](thm.html#V3AsmLevel.codim).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionFibrePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.exists_eq_lineUGen_of_toCrossing_eq_vertexPt_of_forall_specializes
    {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsMaximal] (ht : t ∈ 𝔭) (he : 1 ≤ e)
    (o : Resolution t e) (ho : toCrossing t e o = vertexPt t e 𝔭 ht he)
    (hmax : ∀ o' : Resolution t e, o' ⤳ o → t ∈ ((toSpec t e).base o').asIdeal → o' = o) :
    ∃ k : Fin (e - 1), o = lineUGen t e 𝔭 ht ⟨k, by omega⟩ := by sorry
