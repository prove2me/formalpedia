-- Prove2me | Theorems.Thm_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
-- name    : NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/ce3e966d-795c-5fbf-95d7-b4e6e8e8a3d7
-- title:
--   Translation extension at maximal special points of Z×_R X
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, let $g_K\colon X_K\to\operatorname{Spec}K$ be smooth, separated, locally of finite type and quasi-compact, and let $L_{X_K}$ be a relative group law on $g_K$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}K$, compatible with base change) which is commutative. Let $M$ be a model family for $g_K$ (schemes $X_i$ with structure morphisms $\operatorname{str}_i$ to $\operatorname{Spec}R$ and open immersions of their generic fibres into $X_K$), all $\operatorname{str}_i$ smooth, separated, locally of finite type and quasi-compact, such that $M$ catches index-one points: every point of $X_K$ with values in the fraction field $K'$ of a discrete valuation ring $R'$ which is an index-one extension of $R$ comes from an $R'$-point of some $X_i$ through the chart. Let $d$ be such that $g_K$ is smooth of relative dimension $d$, let $\omega\in\Gamma(\omega^d_{X_K/K},\top)$ be a frame on $\top$, i.e. multiplication by the restriction of $\omega$ is a bijection $\Gamma(X_K,W)\to\Gamma(\omega^d_{X_K/K},W)$ for every open $W$, and assume $\omega$ is left invariant in the following sense: for fields $K\subseteq L\subseteq F$, an $L$-point $a$ and an $F$-point $x$ of $g_K$, and affine opens $U',U''$ of $X_K$ with $F$-algebra structures on their section rings over $K$ through which $x$, respectively the product of the base change of $a$ to $F$ with $x$, factors, any local exterior $d$-forms $\omega'$ on $U'$ and $\omega''$ on $U''$ inducing the restriction of $\omega$ have equal images in $\bigwedge^d_F\Omega_{F/L}$ under the top-form maps. Let $D$ be minimal component data for $(g_K,d,\omega)$ which is $\omega$-minimal, namely each $(D.C\,c).n$ is least among all component readings, and every component reading whose invariant $n$ equals one of these admits, on a neighbourhood of its distinguished special point, an open immersion into some $D.C\,c$ carrying that point to $(D.C\,c).y$ and compatible with the generic-fibre charts. Let $f\colon X\to\operatorname{Spec}R$ be smooth, separated, locally of finite type and quasi-compact, $e$ a morphism from the generic fibre of $f$ to $X_K$ over $\operatorname{Spec}K$ whose underlying morphism is an isomorphism, and for each $c$ let $V_c$ be an open of $(D.C\,c).Y$ and $j_c\colon V_c\to X$ a morphism over $\operatorname{Spec}R$, such that $(D.C\,c).y\in V_c$, every point of $(D.C\,c).Y$ not lying over the closed point of $R$ lies in $V_c$, each $j_c$ is an open immersion, the generic-fibre restriction of $j_c$ followed by $e$ agrees with the generic-fibre restriction of $V_c\hookrightarrow (D.C\,c).Y$ followed by $(D.C\,c).e$, and the images of the $j_c$ cover $X$. Then both of the following hold, differing only in the order of the two factors in the group law: for every scheme $Z$ with $z\colon Z\to\operatorname{Spec}R$ smooth and quasi-compact, every morphism $u_K$ from the generic fibre of $z$ to $X_K$ over $\operatorname{Spec}K$, and every point $\eta$ of $Z\times_{\operatorname{Spec}R}X$ lying over the closed point of $R$ and maximal there (any $y$ specialising to $\eta$ and lying over the closed point equals $\eta$), there are an open $U\ni\eta$ of $Z\times_{\operatorname{Spec}R}X$ and a morphism $\tau\colon U\to X$ over $\operatorname{Spec}R$ such that the induced morphism $U\to Z\times_{\operatorname{Spec}R}X$ with components $U\hookrightarrow Z\times_R X\to Z$ and $\tau$ is an open immersion, and on generic fibres the restriction of $\tau$ followed by $e$ equals the restriction to $U$ of the product, under $L_{X_K}$, of the generic fibre of the first projection followed by $u_K$ and of the generic fibre of the second projection followed by $e$ (in this order in the first clause, in the opposite order in the second).
--
--   This is the translation-extension step in the construction of the Néron model from a weak Néron model, as in Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4(iii), for a commutative group law: near a maximal point of the special fibre of $Z\times_R X$ the translate of the tautological point of $X$ by a $Z$-point of $X_K$ extends to an open immersion into $Z\times_R X$. It is used to assemble the model produced from $\omega$-minimal component data into the Néron model statement for the Jacobian, in [`NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative`](thm.html#NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        letI := gK.sectionsAlgebra U'; letI := gK.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d (gK.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
          gK.topToSections d U' ω' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          gK.topToSections d U'' ω'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F d ω'))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base) :
    (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
    (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)).1) := by sorry
