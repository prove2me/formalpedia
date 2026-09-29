-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/844467e7-a7c7-5239-97de-2c4ab0e94fc7
-- title:
--   Finite geometric kernels imply u locally quasi-finite
-- statement:
--   Let $R$ be a commutative ring and let $gG : G \to \operatorname{Spec} R$ and $gH : H \to \operatorname{Spec} R$ be morphisms of schemes, with $gG$ locally of finite type. Suppose $gG$ and $gH$ carry relative group laws $LG$, $LH$: for each scheme $T$ and each $t : T \to \operatorname{Spec} R$, a multiplication, an identity and an inversion on the set of $T$-points over $t$, that is on pairs $(\varphi, \varphi \circ gG = t)$ (respectively with $gH$), satisfying associativity, the two-sided unit law, left inverses, and compatibility with pullback along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $u$ be a morphism $G \to H$ with $u$ followed by $gH$ equal to $gG$, and assume (hypothesis `hu`) that for all $T$, $t$ and all points $x, y$ of $G$ over $t$, composing $LG.mul\ t\ x\ y$ with $u$ gives $LH.mul\ t$ applied to $x$ followed by $u$ and $y$ followed by $u$. Assume further that for every algebraically closed field $\Omega$ and every $t : \operatorname{Spec} \Omega \to \operatorname{Spec} R$, the set of points $x$ of $G$ over $t$ whose composite with $u$ is $LH.one\ t$ is finite. Then the underlying morphism $u$ is locally quasi-finite. No finiteness hypothesis is imposed on $gH$.
--
--   This is the implication "kernel with finite geometric fibres $\Rightarrow$ locally quasi-finite" for a homomorphism of relative group schemes, in the form of Bosch–Lütkebohmert–Raynaud, Néron Models, 7.3, Lemma 1 ((c) $\Rightarrow$ (d)), here over an arbitrary affine base and with the kernel condition expressed through $\Omega$-valued points. It is used in the study of good reduction of Jacobians, both for the finiteness and flatness criterion for surjective homomorphisms and for multiplication-by-$n$ morphisms in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_of_finite_setOf_schemeHomOverComp_eq_one
    {R : Type u} [CommRing R] {G H : Scheme.{u}}
    {gG : G ⟶ Spec (CommRingCat.of R)} {gH : H ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType gG]
    (LG : RelativeGroupLaw R gG) (LH : RelativeGroupLaw R gH)
    (u : SchemeHomOver gG gH)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t gG),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) u =
        LH.mul t (NeronModelInfra.schemeHomOverComp x u)
          (NeronModelInfra.schemeHomOverComp y u))
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
      {x : SchemeHomOver t gG | NeronModelInfra.schemeHomOverComp x u = LH.one t}.Finite) :
    LocallyQuasiFinite u.1 := by sorry
