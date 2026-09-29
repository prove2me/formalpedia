-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
-- name    : GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/cedeebe7-c2bc-5d68-9932-c8ee84421c99
-- title:
--   Néron–Ogg–Shafarevich: unramified ℓ-power torsion gives an abelian scheme
-- statement:
--   Let $R$ be a discrete valuation ring (an integral domain), $K$ a field that is a fraction field of $R$, and let $g : B \to \operatorname{Spec} R$ be a morphism of schemes equipped with a relative group law `LB`, that is, functorially in a scheme $T$ over $\operatorname{Spec} R$ via $t$, a group structure on the set of $T$-points $\{\varphi : T \to B \mid \varphi \circ g = t\}$ (associative, with unit, with inverses) compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} R$. Assume: this group law is commutative on all $T$-points (`hcomm`); `hN`, the bundle `NeronModelPropertyBundle R K g`, i.e. $g$ is smooth, separated, locally of finite type and quasi-compact, and satisfies the Néron unique extension property that for every scheme $T$ smooth over $\operatorname{Spec} R$ the generic-fibre restriction map on points is bijective; `hBK`, the bundle `AbelianSchemePropertyBundle K` for the second projection $B \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ along $\operatorname{Spec}$ of $R \to K$, i.e. this morphism is smooth and proper, all its fibres (preimages of points of $\operatorname{Spec} K$ under the underlying map) are connected, and it carries some relative group law. Let $\ell$ be a prime whose image in $R$ is a unit, and assume the unramifiedness hypothesis `hunr`: for every valuation subring $A$ of $\overline{K} =$ `AlgebraicClosure K` containing the image of $R$, every $\sigma \in \operatorname{Aut}(\overline{K}/K)$ lying in `A.inertiaSubgroupIn K` (the image of the inertia subgroup inside the decomposition subgroup of $A$), every $v \in \mathbb{N}$ and every $\overline{K}$-point $x$ of the generic fibre that is $\ell^v$-torsion for the base-changed group law `LB.genericFibre K` (iterated multiplication $\ell^v$ times yields the unit), one has $\operatorname{Spec}(\sigma)$ followed by $x$ equal to $x$. Then `AbelianSchemePropertyBundle R g` holds: $g$ is smooth and proper, the preimage under the underlying map of $g$ of each point of $\operatorname{Spec} R$ is connected, and $g$ admits a relative group law.
--
--   This is the substantial implication of the Néron–Ogg–Shafarevich criterion for good reduction, in the form: a Néron model, with commutative relative group law, of an abelian variety over $K$ whose $\ell$-power torsion is unramified ($\ell$ invertible on the base) is already an abelian scheme over $R$. It is used in the treatment of good reduction for fake elliptic curves and Jacobians, and in a variant over Henselian local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓu : IsUnit (ℓ : R))
    (hunr : ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (v : ℕ) (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1) :
    AbelianSchemePropertyBundle R g := by sorry
