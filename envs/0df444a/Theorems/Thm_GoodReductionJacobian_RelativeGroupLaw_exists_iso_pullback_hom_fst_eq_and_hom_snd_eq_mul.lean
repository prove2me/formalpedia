-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/95374a8d-2705-58dd-a14d-106f4258b253
-- title:
--   Translation by a point trivialises T ×_R G
-- statement:
--   Let $R$ be a commutative ring, let $G$ and $T$ be schemes, and let $g \colon G \to \operatorname{Spec} R$ be a morphism of schemes. Let $L$ be a relative group law on $g$, that is: data assigning to every $R$-scheme $t \colon T' \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set $\{\varphi \colon T' \to G \mid \varphi \circ g = t\}$ of morphisms to $G$ lying over $t$, satisfying associativity, both unit laws and the left inverse law for each such $t$, together with naturality of the multiplication: for $\psi \colon T'' \to T'$ with $\psi$ followed by $t$ equal to $t''$, precomposition with $\psi$ carries the product of two points over $t$ to the product of their precompositions. Let $t \colon T \to \operatorname{Spec} R$ be a morphism, and let $a$ be a morphism $T \to G$ with $a$ followed by $g$ equal to $t$. Then there exists an isomorphism $\sigma$ of the fibre product $T \times_{\operatorname{Spec} R} G$ with itself such that $\sigma$ followed by the first projection is the first projection, while $\sigma$ followed by the second projection is the underlying morphism of the product, formed by $L$ over the base morphism given by the first projection followed by $t$, of the point obtained by precomposing $a$ with the first projection and the point given by the second projection (which lies over that base morphism by the pullback condition).
--
--   This is the statement that translation by a $T$-valued point $a$ of $G$ is an automorphism of $T \times_R G$ over $T$, the shear $(\zeta, x) \mapsto (\zeta, a(\zeta) \cdot x)$ attached to a group law on the functor of points of $g$. It is used in the analysis of generic fibres and stalks of the relative group law, being cited by [`NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift`](thm.html#NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
    {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    ∃ σ : pullback t g ≅ pullback t g,
      σ.hom ≫ pullback.fst t g = pullback.fst t g ∧
      σ.hom ≫ pullback.snd t g =
        (L.mul (pullback.fst t g ≫ t) ⟨pullback.fst t g ≫ a.1, by rw [Category.assoc, a.2]⟩
          ⟨pullback.snd t g, pullback.condition.symm⟩).1 := by sorry
