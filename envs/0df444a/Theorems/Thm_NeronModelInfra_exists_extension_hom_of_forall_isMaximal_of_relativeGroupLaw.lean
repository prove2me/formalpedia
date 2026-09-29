-- Prove2me | Theorems.Thm_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
-- name    : NeronModelInfra.exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/dd6f052f-0144-54ef-8346-35a1ba53536d
-- title:
--   Global extension of a homomorphic endomorphism of G_ℚ
-- statement:
--   Let $g\colon G\to\operatorname{Spec}\mathbb Z$ be a separated, flat morphism, locally of finite type, and let $L$ be a relative group law on $g$ over $\mathbb Z$, that is, a group structure on the set $\{\varphi\colon T\to G \mid \varphi\circ = t\}$ of $T$-points over each $t\colon T\to\operatorname{Spec}\mathbb Z$, compatible with composition in $T$. Write $G_{\mathbb Q}$ for the pullback of $g$ along $\operatorname{Spec}$ of $\mathbb Z\to\mathbb Q$, with its second projection as structure morphism, and let $\varphi_\eta$ be an endomorphism of $G_{\mathbb Q}$ over $\operatorname{Spec}\mathbb Q$. Assume: (i) for every $s\colon T\to\operatorname{Spec}\mathbb Q$ and all $T$-points $x,y$ of $G_{\mathbb Q}$ over $s$, composing with $\varphi_\eta$ turns the base-changed law $L_{\mathbb Q}$ into itself, $\varphi_\eta\circ L_{\mathbb Q}(x,y)=L_{\mathbb Q}(\varphi_\eta\circ x,\varphi_\eta\circ y)$; (ii) $a,b\colon \iota'\to \operatorname{Hom}(\operatorname{Spec}\overline{\mathbb Q},G)$ are families whose composites with $g$ are both the structure morphism $\operatorname{Spec}$ of $\mathbb Z\to\overline{\mathbb Q}$, and for each $i$, any $z,z_t\colon\operatorname{Spec}\overline{\mathbb Q}\to G_{\mathbb Q}$ with first projections $a_i$ and $b_i$ satisfy $z_t=\varphi_\eta\circ z$; (iii) for every maximal ideal $\mathfrak m\subset\mathbb Z$ there are a localisation $A$ of $\mathbb Z$ at $\mathfrak m$, an $A$-algebra structure on $\mathbb Q$ compatible with $\mathbb Z$, and a morphism $g_A\colon G_A\to G$ over $g$ (i.e. $g\circ g_A$ equals $g$ composed with the first projection) such that every $j\colon G_{\mathbb Q}\to G_A$ commuting with the first projections satisfies $g_A\circ j=\mathrm{pr}_1\circ\varphi_\eta$. Then there exists an endomorphism $\varphi$ of $G$ over $\operatorname{Spec}\mathbb Z$ such that $\varphi\circ\mathrm{pr}_1=\mathrm{pr}_1\circ\varphi_\eta$ on $G_{\mathbb Q}$, such that $\varphi\circ L(x,y)=L(\varphi\circ x,\varphi\circ y)$ for all $T$-points $x,y$ over every $t\colon T\to\operatorname{Spec}\mathbb Z$, and such that $b_i=\varphi\circ a_i$ for all $i\in\iota'$.
--
--   This is the local-to-global gluing step for endomorphisms of a flat separated group scheme over $\mathbb Z$: prime-by-prime extensions of an endomorphism of the generic fibre are assembled into a single endomorphism over $\mathbb Z$, which automatically remains a homomorphism for the relative group law and preserves the prescribed pairs of $\overline{\mathbb Q}$-points. It is used by [`ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic`](thm.html#ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic), where the per-prime hypothesis is supplied separately at the distinguished prime and away from it; the proof cites [`NeronModelInfra.existsUnique_extension_of_exists_isLocalization_atPrime`](thm.html#NeronModelInfra.existsUnique_extension_of_exists_isLocalization_atPrime) and [`GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre`](thm.html#GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem NeronModelInfra.exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g] [Flat g]
    (L : RelativeGroupLaw ℤ g)
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (hhom : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
        (x y : SchemeHomOver s (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
      NeronModelInfra.schemeHomOverComp
          ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    {ι' : Type} (a b : ι' → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ G))
    (hab : ∀ (i : ι') (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
      z ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = a i →
      zt ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = b i →
      zt = z ≫ φη.1)
    (ha : ∀ i : ι', a i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hb : ∀ i : ι', b i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (h : ∀ (𝔪 : Ideal ℤ) [𝔪.IsMaximal], ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℤ A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A ℚ) (_ : IsScalarTower ℤ A ℚ)
        (gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ⟶ G),
        gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ≫ g ∧
        ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
            pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))),
          j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) =
            pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
          j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ)) :
    ∃ φ : SchemeHomOver g g,
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ φ.1 =
        φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s g),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ i : ι', b i = a i ≫ φ.1 := by sorry
