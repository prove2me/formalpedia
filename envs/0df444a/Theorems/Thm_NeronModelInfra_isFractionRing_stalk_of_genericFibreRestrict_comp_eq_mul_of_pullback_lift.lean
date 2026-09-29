-- Prove2me | Theorems.Thm_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
-- name    : NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/beeeb89e-018e-57b7-a71a-a0f1ac8485f0
-- title:
--   Translation by a K-point is birational at η
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$ (via `IsFractionRing R K`). Let $g_K : X_K \to \operatorname{Spec} K$ be smooth, separated, locally of finite type and quasi-compact, equipped with a `RelativeGroupLaw` $L_{X_K}$ over $K$, i.e. a functorial group structure on sections of $g_K$ over $K$-schemes, and smooth of relative dimension $d$; let $\omega$ be a global section of the $d$-th exterior power `topDifferentials` of the Kähler module of $g_K$. Let $f : X \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, with $e$ a morphism $X \times_{\operatorname{Spec} R} \operatorname{Spec} K \to X_K$ over $\operatorname{Spec} K$ whose underlying scheme morphism is an isomorphism; let $z : Z \to \operatorname{Spec} R$ be smooth and quasi-compact, and $u_K$ a morphism from the generic fibre of $z$ to $X_K$ over $\operatorname{Spec} K$. Fix a point $\eta$ of $Z \times_{\operatorname{Spec} R} X$, a `ComponentReading` $T$ for $(R,K,g_K,d,\omega)$ — in particular a smooth, locally of finite type $R$-scheme $T.f : Y_T \to \operatorname{Spec} R$ together with an open immersion $T.e$ of its generic fibre into $X_K$, a point of $Y_T$ over the closed point maximal among its specialisations with discrete valuation stalk, and the attendant algebra and basis data — an open $U_0 \ni \eta$ of $Z \times_{\operatorname{Spec} R} X$, and a morphism $\tau_0 : U_0 \to Y_T$ over $\operatorname{Spec} R$, the structure morphism of $U_0$ being $U_0 \hookrightarrow Z \times_{\operatorname{Spec} R} X \to Z \to \operatorname{Spec} R$. Assume ($h\tau_0$) that the generic fibre of $\tau_0$ followed by $T.e$ equals the base change of $U_0 \hookrightarrow Z \times_{\operatorname{Spec} R} X$ to $K$ followed by the $L_{X_K}$-product of $u_K \circ (\mathrm{pr}_Z)_K$ and $e \circ (\mathrm{pr}_X)_K$; in other words $T.e(\tau_0(\zeta,x)) = u_K(\zeta)\cdot e(x)$ on generic fibres. Let $v : U_0 \to Z \times_{\operatorname{Spec} R} Y_T$ satisfy $v$ followed by $\mathrm{pr}_Z$ equals $U_0 \hookrightarrow Z \times_{\operatorname{Spec} R} X \to Z$, and $v$ followed by $\mathrm{pr}_{Y_T}$ equals $\tau_0$. The conclusion asserts that the local ring of $U_0$ at $\eta$ and the local ring of $Z \times_{\operatorname{Spec} R} Y_T$ at $v(\eta)$ are integral domains, and that, for the algebra structure obtained by composing the stalk map of $v$ at $\eta$ with the localisation map, $\operatorname{Frac}(\mathcal{O}_{U_0,\eta})$ is a fraction field of $\mathcal{O}_{Z \times_R Y_T,\,v(\eta)}$; that is, $v$ is birational at $\eta$.
--
--   This is the birationality step in the construction of Néron models by gluing translates, corresponding to Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4(iii): translating by a $K$-point of the group scheme does not change the function field of the local ring at a point. It feeds the order computation at $\eta$ and the étale-implies-open criterion used in the translation-extension arguments, being cited by [`NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul`](thm.html#NeronModelInfra.exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul) and [`NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative`](thm.html#NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift.lean

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

theorem NeronModelInfra.isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
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
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1) :
    ∃ (_ : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
      (_ : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩))),
      letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := by sorry
