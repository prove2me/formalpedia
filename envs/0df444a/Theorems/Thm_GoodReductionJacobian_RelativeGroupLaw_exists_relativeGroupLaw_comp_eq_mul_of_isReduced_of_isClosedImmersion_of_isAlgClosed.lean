-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/4bbffe4a-dc7d-537b-8f2c-fbea1f0a34da
-- title:
--   Reduced closed subscheme whose k-points form a subgroup
-- statement:
--   Let $k$ be an algebraically closed field, let $g : G \to \operatorname{Spec} k$ be a morphism of schemes that is locally of finite type, and let $L$ be a relative group law on $g$: a structure assigning to every $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi : T \to G \mid \varphi \text{ followed by } g = t\}$, satisfying associativity, the two unit laws and left inversion, and with the multiplication compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Let $z : Z \to \operatorname{Spec} k$ be a further $k$-scheme and $\iota$ a morphism $Z \to G$ with $\iota$ followed by $g$ equal to $z$, such that the underlying morphism is a closed immersion and $Z$ is reduced. Assume, for the sections of $z$ over the identity of $\operatorname{Spec} k$ (the $k$-points of $Z$): some such point composes with $\iota$ to the unit of $L$ at the identity; for any two such points $x,y$ some such point composes with $\iota$ to $L$-product of $\iota\circ x$ and $\iota\circ y$; and for any such $x$ some such point composes with $\iota$ to the $L$-inverse of $\iota\circ x$. Then there is a relative group law $L_Z$ on $z$ such that for every $k$-scheme $t : T \to \operatorname{Spec} k$ and all $T$-points $x,y$ of $Z$ over $t$, the composite of $L_Z$-product of $x$ and $y$ with $\iota$ equals the $L$-product of $\iota\circ x$ and $\iota\circ y$; compatibility of $\iota$ with unit and inversion is not asserted.
--
--   This is the classical statement that a reduced closed subscheme of a group scheme locally of finite type over an algebraically closed field whose $k$-points form a subgroup is a closed subgroup scheme, here in the functor-of-points formulation used for group laws on Jacobians and Néron models. It is used in the construction of homomorphisms of abelian schemes from conditions on points, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hom_mapPt_eq_of_forall_curve_eq_mapPt_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isReduced_of_isClosedImmersion_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] (L : RelativeGroupLaw k g)
    {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of k)} (ι : SchemeHomOver z g)
    [IsClosedImmersion ι.1] [IsReduced Z]
    (hone : ∃ o : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      NeronModelInfra.schemeHomOverComp o ι = L.one (𝟙 (Spec (CommRingCat.of k))))
    (hmul : ∀ x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
        NeronModelInfra.schemeHomOverComp w ι =
          L.mul (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)
            (NeronModelInfra.schemeHomOverComp y ι))
    (hinv : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
      ∃ w : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z,
        NeronModelInfra.schemeHomOverComp w ι =
          L.inv (𝟙 (Spec (CommRingCat.of k))) (NeronModelInfra.schemeHomOverComp x ι)) :
    ∃ LZ : RelativeGroupLaw k z,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t z),
        NeronModelInfra.schemeHomOverComp (LZ.mul t x y) ι =
          L.mul t (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι) := by sorry
