-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away
-- name    : GoodReductionJacobian.exists_relativeGroupLaw_one_eq_of_forall_exists_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/70b20128-cf99-57f5-b38f-838c08c5ece8
-- title:
--   Gluing relative group laws from basic opens of the base
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism, and let $e$ be a section of $f$, i.e. a morphism $e.1 : \operatorname{Spec} R \to A$ with $e.1$ followed by $f$ equal to the identity. Here a `RelativeGroupLaw` for a morphism to $\operatorname{Spec} R$ is a structure giving, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$, a multiplication, a unit and an inversion on the set of $T$-points over $t$ (morphisms $T \to A$ composing with $f$ to $t$), subject to associativity, both unit laws, left inverses, and naturality of the multiplication alone under any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume: (i) for every point $s \in \operatorname{Spec} R$ there is $r \in R$ with $r \notin s$ such that the base change of $f$ along $\operatorname{Spec} R[1/r] \to \operatorname{Spec} R$ (the second pullback projection) carries a relative group law over $R[1/r]$ whose unit at the identity base is the morphism induced by $e$ on the base change; and (ii) for every $r \in R$, two relative group laws on that base change with the same unit at the identity base are equal. Then $f$ carries a relative group law over $R$ whose unit at the identity base is exactly $e$.
--
--   This is the descent step which produces a group structure on an $R$-scheme with a given section from group structures on the base changes over a cover of $\operatorname{Spec} R$ by basic open affines, local uniqueness of the group law with prescribed unit serving as the cocycle condition. It is used in the construction of the group law on a smooth projective relative curve Jacobian over a Noetherian base, in [`GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing`](thm.html#GoodReductionJacobian.exists_relativeGroupLaw_one_eq_and_isCommutative_of_smooth_of_isClosedImmersion_proj_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_relativeGroupLaw_one_eq_of_forall_exists_away.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_relativeGroupLaw_one_eq_of_forall_exists_away
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hloc : ∀ s : Spec (CommRingCat.of R), ∃ (r : R), r ∉ s.asIdeal ∧
      ∃ L : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))),
        (L.one (𝟙 _)).1 = pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]))
    (huniq : ∀ (r : R) (L L' : RelativeGroupLaw (Localization.Away r)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))),
        L.one (𝟙 _) = L'.one (𝟙 _) → L = L') :
    ∃ L : RelativeGroupLaw R f, L.one (𝟙 _) = e := by sorry
