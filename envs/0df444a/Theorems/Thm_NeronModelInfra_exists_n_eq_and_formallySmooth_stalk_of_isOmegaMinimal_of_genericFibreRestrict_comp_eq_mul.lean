-- Prove2me | Theorems.Thm_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
-- name    : NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/d6061156-ab8e-5e13-bc23-1edf911a6017
-- title:
--   Minimal order and formal smoothness at a maximal special point
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, and let $g_K\colon X_K\to\operatorname{Spec}K$ be smooth, separated, locally of finite type and quasi-compact, of relative dimension $d$, equipped with a relative group law `LXK` over $K$ (functorial multiplication, unit and inverse on $T$-points for $T$ over $\operatorname{Spec}K$, with the group axioms and naturality). Let $\omega$ be a global section of the $d$-th determinant $\Gamma(g_K.\mathrm{topDifferentials}\,d,\top)$ which is a frame on $\top$, i.e. for every open $W$ multiplication by the restriction of $\omega$ is a bijection $\Gamma(X_K,W)\to\Gamma(g_K.\mathrm{topDifferentials}\,d,W)$; the hypothesis `hleft` expresses left invariance pointwise: for fields $K\subseteq L\subseteq F$, an $L$-point $a$, an $F$-point $x$ of $g_K$ and affine opens $U',U''$ (with the relevant algebra structures and scalar towers) through which $x$, respectively the product of the base change of $a$ with $x$, factor, any $d$-forms $\omega',\omega''$ on $U',U''$ whose images under `topToSections` restrict $\omega$ satisfy $\mathrm{topFormMap}\,K\,L\,\Gamma(X_K,U'')\,F\,d\,\omega''=\mathrm{topFormMap}\,K\,L\,\Gamma(X_K,U')\,F\,d\,\omega'$. Let $D$ be minimal component data for $(g_K,d,\omega)$ which is $\omega$-minimal: each $D.C\,c$ has invariant $n$ least among all component readings, and every reading whose invariant equals some $(D.C\,c).n$ admits, on a neighbourhood of its marked point, an open immersion into $(D.C\,c).Y$ carrying the marked point to $(D.C\,c).y$ and compatible with the generic-fibre charts. Let $f\colon X\to\operatorname{Spec}R$ be smooth, separated, locally of finite type and quasi-compact, and $e$ an isomorphism of the generic fibre $\operatorname{pullback.snd} f\,(\mathrm{specGenericFibreInclusion}\,R\,K)$ onto $g_K$ over $K$; let $V_c\subseteq (D.C\,c).Y$ be opens and $j_c\colon V_c\to X$ morphisms over $R$ which are open immersions, with $(D.C\,c).y\in V_c$, with $V_c$ containing every point of $(D.C\,c).Y$ not lying over the closed point of $R$, whose generic fibres followed by $e$ agree with the generic fibre of $V_c\hookrightarrow (D.C\,c).Y$ followed by $(D.C\,c).e$, and whose images cover $X$. Let $z\colon Z\to\operatorname{Spec}R$ be smooth and quasi-compact, $u_K$ a $K$-morphism from the generic fibre of $z$ to $g_K$, and $\eta$ a point of $Z\times_R X$ lying over the closed point of $R$ and maximal among such (any point specialising to $\eta$ and lying over the closed point equals $\eta$). Let $T$ be a component reading for $(g_K,d,\omega)$, let $U_0$ be an open of $Z\times_R X$ containing $\eta$ and $\tau_0\colon U_0\to T.Y$ a morphism over $R$ whose generic fibre followed by $T.e$ is the translation $(\zeta,x)\mapsto u_K(\zeta)\cdot e(x)$, formulated as the equality `hτ₀` of morphisms of generic fibres using `LXK.mul`; let $v\colon U_0\to Z\times_R T.Y$ have components the inclusion followed by the projection to $Z$ and $\tau_0$, and assume $T.y$ specialises to $\tau_0(\eta)$. Then there is $c$ with $T.n=(D.C\,c).n$, and the stalk of $U_0$ at $\eta$ is formally smooth as an algebra over the stalk of $Z\times_R T.Y$ at $v(\eta)$, the algebra structure being the one induced by the stalk map of $v$.
--
--   This is the technical core of the theory of group smoothening in Bosch–Lütkebohmert–Raynaud 4.3 (Proposition 4(iii), together with Lemmas 1 and 3): at a maximal point of the special fibre of $Z\times_R X$ the invariant form attains the minimal order, so the reading of the translation chart realises a component of the minimal data and the translation is formally smooth there. It is used by [`NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative`](thm.html#NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative), where the first conclusion feeds the representability clause of $\omega$-minimality and the second supplies the formal smoothness needed to extend the translation to an open immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.lean

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

theorem NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
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
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η)
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩) :
    (∃ c : D.ι, T.n = (D.C c).n) ∧
      letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := by sorry
