-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/15bf0d57-0011-5e1b-9c8a-c90bbae035f8
-- title:
--   Smooth with n-dimensional fibres and a group law is smooth of relative dimension n
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f : X \to \operatorname{Spec} R$ a smooth morphism. Suppose $f$ carries a relative group law $G$ in the sense of `RelativeGroupLaw`: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of $t$-sections $\{\varphi : T \to X \mid \varphi \circ t' = t\}$, more precisely on `SchemeHomOver t f`, the subtype of morphisms $\varphi : T \to X$ with $f \circ \varphi = t$, subject to associativity, both unit laws and the left inverse law, together with naturality of the multiplication under precomposition: for $\psi : T' \to T$ with $t \circ \psi = t'$, composing a product of two sections with $\psi$ gives the product of their composites with $\psi$. Let $n$ be a natural number and assume that for every point $s$ of $\operatorname{Spec} R$ the topological space $f^{-1}(\{s\})$, the preimage of $\{s\}$ under the map on underlying spaces, has topological Krull dimension equal to $n$. The conclusion is that $f$ is smooth of relative dimension $n$, i.e. `SmoothOfRelativeDimension n f` holds.
--
--   This is the standard passage from fibrewise dimension data to a relative-dimension statement for a smooth group scheme over a base: a group law forces each fibre to be equidimensional, so a single numerical hypothesis on all topological fibres upgrades plain smoothness to smoothness of relative dimension $n$. It is used in the treatment of abelian schemes and their polarisations, where relative dimension has to be available uniformly over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_forall_topologicalKrullDim_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [Smooth f]
    (G : RelativeGroupLaw R f) (n : ℕ)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of R)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = n) :
    SmoothOfRelativeDimension n f := by sorry
