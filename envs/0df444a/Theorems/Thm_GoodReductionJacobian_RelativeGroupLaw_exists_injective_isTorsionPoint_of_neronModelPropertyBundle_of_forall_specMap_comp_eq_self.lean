-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/49484ac7-ee69-5c3b-9623-510250413cae
-- title:
--   Counted Serre–Tate lemma: ℓ^{2dv} torsion points on the special fibre
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain), $K$ a field which is its fraction field, $B$ a scheme and $g : B \to \operatorname{Spec} R$ a morphism. Let `LB` be a `RelativeGroupLaw` for $g$, that is, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, unit and inverse on the set `SchemeHomOver t g` of morphisms $T \to B$ over $\operatorname{Spec} R$ commuting with $t$, satisfying associativity, the two unit laws, left inverse, and naturality under precomposition with morphisms $\psi$ over $\operatorname{Spec} R$; assume in addition (`hcomm`) that every such multiplication is commutative. Assume `hN`: $g$ is smooth, separated, locally of finite type and quasi-compact, and has the Néron mapping property, namely for every smooth $t : T \to \operatorname{Spec} R$ restriction to the generic fibre is a bijection on points over $t$. Assume `hBK`: the generic fibre structure morphism $\operatorname{pullback.snd}$ of $g$ along $\operatorname{Spec} K \to \operatorname{Spec} R$ is smooth, proper, has connected fibres over each point of $\operatorname{Spec} K$, and admits some relative group law; let $d$ be a natural number for which this morphism is smooth of relative dimension $d$. Let $\ell$ be a natural number whose image in $R$ is a unit. Assume `hunr`: for every valuation subring $A$ of $\operatorname{AlgebraicClosure} K$ containing the image of $R$, every $K$-automorphism $\sigma$ of $\operatorname{AlgebraicClosure} K$ lying in the inertia subgroup of $A$ over $K$ (the image of $A$'s inertia subgroup inside the decomposition subgroup), every $v$, and every point $x$ of the generic fibre over $\operatorname{Spec}$ of $\operatorname{AlgebraicClosure} K$ which is killed by $\ell^{v}$ for the base-changed group law `LB.genericFibre K` (i.e. the $\ell^{v}$-fold iterate of the multiplication by $x$ starting from the unit is the unit), the composite of $\operatorname{Spec}\sigma$ with $x$ equals $x$. Finally let $k'$ be an algebraically closed field which is an $R$-algebra such that the structure map kills the maximal ideal of $R$, and let $v$ be a natural number. Then there is an injection from $\operatorname{Fin}(\ell^{2dv})$ into the set of points $y$ of $B$ over $\operatorname{Spec}(R \to k')$ with $\ell^{v} y$ equal to the unit for `LB`.
--
--   This is the counted form of Lemma 2 of Serre and Tate's §1 on good reduction of abelian varieties, as it enters the implication "unramified $\ell$-power torsion $\Rightarrow$ good reduction": the special fibre of the Néron model carries at least $\ell^{2dv}$ geometric points killed by $\ell^{v}$, obtained by spreading out unramified generic $\ell^{v}$-torsion and specialising. It is used in the proof that a Néron model with unramified $\ell$-power torsion on its generic fibre is itself an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (d : ℕ) [SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K))]
    (ℓ : ℕ) (hℓu : IsUnit (ℓ : R))
    (hunr : ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (v : ℕ) (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (ℓ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1)
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra R k']
    (hk' : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0) (v : ℕ) :
    ∃ r : Fin (ℓ ^ (2 * d * v)) →
        {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
          LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) (ℓ ^ v) y},
      Function.Injective r := by sorry
