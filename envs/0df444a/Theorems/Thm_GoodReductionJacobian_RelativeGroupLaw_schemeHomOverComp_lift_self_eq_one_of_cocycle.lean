-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeHomOverComp_lift_self_eq_one_of_cocycle
-- name    : GoodReductionJacobian.RelativeGroupLaw.schemeHomOverComp_lift_self_eq_one_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ac29f029-94e3-5300-ba24-23c075181313
-- title:
--   A cocycle for a relative group law is trivial on the diagonal
-- statement:
--   Let $R$ be a commutative ring, let $gN \colon N \to \operatorname{Spec} R$ be a scheme over $R$, and let $L$ be a `RelativeGroupLaw R gN`: data assigning to every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} R$ a multiplication, a unit and an inversion on the set of morphisms $\varphi \colon T \to N$ with $\varphi$ followed by $gN$ equal to $t$, subject to associativity, the two unit laws, the left inverse law, and naturality of the multiplication under precomposition by a morphism $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $q \colon S' \to \operatorname{Spec} R$ be a morphism and let $g$ be a point of $N$ over the fibre product $S' \times_{\operatorname{Spec} R} S'$, i.e. a morphism $\mathrm{pullback}\ q\ q \to N$ whose composite with $gN$ is the first projection followed by $q$. Assume the cocycle identity on the triple product $P = (S' \times S') \times_{\mathrm{pr}_2, S', \mathrm{pr}_1} (S' \times S')$: the $L$-product of the pullback of $g$ along the first projection $P \to S' \times S'$ and of the pullback of $g$ along the second projection equals the pullback of $g$ along the morphism $P \to S' \times S'$ obtained by lifting the outer two coordinates (the first projection followed by $\mathrm{pr}_1$, and the second projection followed by $\mathrm{pr}_2$), all three being points over the structure morphism of $P$. Then for every scheme $T$ and every morphism $t \colon T \to S'$, the pullback of $g$ along the diagonal point $(t,t) \colon T \to S' \times_{\operatorname{Spec} R} S'$ equals the unit $L.\mathrm{one}\,(t \circ q)$ of the group of $T$-points of $N$ over $t$ followed by $q$.
--
--   This is the standard normalisation statement for a Čech $1$-cocycle with coefficients in a group object written in terms of a relative group law: a cocycle evaluated on the diagonal is the identity. It is used in the descent arguments that trivialise such a cocycle over a base with good local properties, being cited in the construction of the associated solution scheme and in the verification of its smoothness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_schemeHomOverComp_lift_self_eq_one_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.schemeHomOverComp_lift_self_eq_one_of_cocycle
    {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    {S' : Scheme.{0}} (q : S' ⟶ Spec (CommRingCat.of R))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
    {T : Scheme.{0}} (t : T ⟶ S') :
    GoodReductionJacobian.schemeHomOverComp (pullback.lift t t rfl)
        (by rw [← Category.assoc, pullback.lift_fst]) g = L.one (t ≫ q) := by sorry
