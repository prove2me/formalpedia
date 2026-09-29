-- Prove2me | Theorems.Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
-- name    : NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e49a611e-9637-53a3-bbde-5a9f1479be41
-- title:
--   Formally smooth birational translation extends to an open immersion
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, let $g_K\colon X_K\to\operatorname{Spec}K$ be smooth, separated, locally of finite type and quasi-compact of relative dimension $d$, equipped with a relative group law $L_{X_K}$ (functorial multiplication, unit and inverse on $K$-points of $g_K$, with the group axioms and naturality), and let $\omega$ be a global section of the $d$-th exterior power of the Kähler module of $g_K$. Let $D$ be minimal component data for $(R,K,g_K,d,\omega)$ — a finite nonempty family $C_c$ of component readings, each with separated quasi-compact structure morphism, generic-fibre comparison $(D.C\,c).e$ an isomorphism, every closed-fibre point a specialisation of $(D.C\,c).y$, and distinct indices pairwise inequivalent — satisfying `IsOmegaMinimal`: the invariant $n$ of each $C_c$ is minimal among all component readings, and every component reading $T$ with $T.n=(D.C\,c).n$ for some $c$ admits an open $W\ni T.y$ and an open immersion $\varepsilon\colon W\to (D.C\,c).Y$ over $R$ carrying $T.y$ to $(D.C\,c).y$ and compatible with the comparisons $T.e$, $(D.C\,c).e$ on generic fibres. Let $f\colon X\to\operatorname{Spec}R$ be smooth, separated, locally of finite type and quasi-compact, $e$ a $K$-morphism from the generic fibre of $f$ to $X_K$ with $e$ an isomorphism, and let $V_c\subseteq (D.C\,c).Y$ be opens containing $(D.C\,c).y$ and containing every point not over the closed point of $\operatorname{Spec}R$, with $R$-morphisms $j_c\colon V_c\to X$ that are open immersions, compatible with $e$ and $(D.C\,c).e$ on generic fibres, and whose images cover $X$. Let $z\colon Z\to\operatorname{Spec}R$ be smooth and quasi-compact, $u_K$ a $K$-morphism from the generic fibre of $z$ to $X_K$, and let $\eta\in Z\times_R X$ lie over the closed point of $\operatorname{Spec}R$ and be maximal in the sense that any $y$ specialising to $\eta$ and lying over the closed point equals $\eta$. Let $T$ be a component reading, $U_0\ni\eta$ an open of $Z\times_R X$ and $\tau_0\colon U_0\to T.Y$ an $R$-morphism whose generic fibre satisfies $T.e\circ\tau_0=L_{X_K}(u_K\circ\mathrm{pr}_Z,\,e\circ\mathrm{pr}_X)$ after restriction to $U_0$; let $v\colon U_0\to Z\times_R T.Y$ have components $\mathrm{pr}_Z|_{U_0}$ and $\tau_0$; assume $T.y$ specialises to $\tau_0(\eta)$, $T.n=(D.C\,c).n$ for some $c$, the stalks of $U_0$ at $\eta$ and of $Z\times_R T.Y$ at $v(\eta)$ are domains, the stalk map of $v$ at $\eta$ exhibits $\operatorname{Frac}$ of the stalk of $U_0$ at $\eta$ as a fraction field of the stalk at $v(\eta)$, and this stalk map is formally smooth. Then there exist an open $U\ni\eta$ of $Z\times_R X$ and an $R$-morphism $\tau\colon U\to X$ such that $(\mathrm{pr}_Z|_U,\tau)\colon U\to Z\times_R X$ is an open immersion and the generic fibre of $\tau$ satisfies the same translation identity $e\circ\tau=L_{X_K}(u_K\circ\mathrm{pr}_Z,\,e\circ\mathrm{pr}_X)$ on $U$.
--
--   This is the step in the Néron-model construction that lands a left translate inside the glued model $X$: under birationality and formal smoothness of the comparison morphism $v$ at the maximal point $\eta$ of the special fibre, the translation morphism defined on a neighbourhood of $\eta$ with values in a component reading is replaced by one with values in $X$ whose graph is an open immersion. It supplies the existential clause used by [`NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative`](thm.html#NeronModelInfra.forall_nhds_translation_extension_isOpenImmersion_of_isOmegaMinimal_of_openCover_of_isCommutative) to make the group law on the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal.lean

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

theorem NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
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
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩)
    (hn : ∃ c : D.ι, T.n = (D.C c).n)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : letI : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
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
                ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1 := by sorry
