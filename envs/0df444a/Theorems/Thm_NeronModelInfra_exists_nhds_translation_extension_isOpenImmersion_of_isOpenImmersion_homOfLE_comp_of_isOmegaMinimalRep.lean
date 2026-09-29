-- Prove2me | Theorems.Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep
-- name    : NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/21e5dbdb-6160-520a-aff7-3a8f3734d0b8
-- title:
--   Landing a translate in X from a chart on an ω-minimal component
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $g_K \colon X_K \to \operatorname{Spec} K$ be smooth, separated, locally of finite type and quasi-compact, let $L_{X_K}$ be a relative group law on $g_K$ (a functorial group structure on the sets of sections $\{\varphi : T \to X_K \mid \varphi \text{ over } \operatorname{Spec} K\}$), let $g_K$ be smooth of relative dimension $d$, and let $\omega$ be a global section of the $d$-th determinant of the Kähler module of $g_K$. Let $D$ be minimal component data for $(R,K,g_K,d,\omega)$, assumed $\omega$-minimal (each $(D.C\,c).n$ is minimal among all component readings, and every reading whose invariant equals some $(D.C\,c).n$ admits an open-immersion chart onto a neighbourhood of $(D.C\,c).y$ compatible with the generic-fibre identifications). Let $f \colon X \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, and $e$ a morphism from the generic fibre $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $\operatorname{Spec} K$ whose underlying morphism is an isomorphism. Assume given opens $V_c \subseteq (D.C\,c).Y$ containing $(D.C\,c).y$ and containing every point not lying over the closed point of $\operatorname{Spec} R$, together with morphisms $j_c \colon V_c \to X$ over $\operatorname{Spec} R$ that are open immersions, satisfy on generic fibres $e \circ (j_c)_K = (D.C\,c).e|_{(V_c)_K}$, and whose images cover $X$. Let $z \colon Z \to \operatorname{Spec} R$ be smooth and quasi-compact, $u_K$ a morphism from the generic fibre of $z$ to $X_K$ over $\operatorname{Spec} K$, and $\eta$ a point of $Z \times_{\operatorname{Spec} R} X$ lying over the closed point of $\operatorname{Spec} R$ and maximal for this property (any point specialising to $\eta$ and lying over the closed point equals $\eta$). Let $T$ be a component reading for $(R,K,g_K,d,\omega)$; let $U_0 \ni \eta$ be open in $Z \times_{\operatorname{Spec} R} X$ and $\tau_0 \colon U_0 \to T.Y$ a morphism over $\operatorname{Spec} R$ whose generic-fibre restriction followed by $T.e$ is the product, under $L_{X_K}$, of $u_K \circ \mathrm{pr}_Z$ and $e \circ \mathrm{pr}_X$ restricted to $U_0$. Let $v \colon U_0 \to Z \times_{\operatorname{Spec} R} T.Y$ have components $\mathrm{pr}_Z|_{U_0}$ and $\tau_0$, let $U_1$ with $\eta \in U_1 \le U_0$ be such that $v$ restricted to $U_1$ is an open immersion, and assume $\tau_0(\eta) = T.y$. Finally let $c$ be an index of $D$, $W \subseteq T.Y$ an open containing $T.y$, and $\varepsilon \colon W \to (D.C\,c).Y$ a morphism over $\operatorname{Spec} R$ that is an open immersion with $\varepsilon(T.y) = (D.C\,c).y$ and $(D.C\,c).e \circ \varepsilon_K = T.e|_{W_K}$. The conclusion asserts the existence of an open $U \ni \eta$ of $Z \times_{\operatorname{Spec} R} X$ and a morphism $\tau \colon U \to X$ over $\operatorname{Spec} R$ such that $(\mathrm{pr}_Z|_U, \tau) \colon U \to Z \times_{\operatorname{Spec} R} X$ is an open immersion and, on generic fibres, the restriction of $\tau$ followed by $e$ equals the $L_{X_K}$-product of $u_K \circ \mathrm{pr}_Z$ and $e \circ \mathrm{pr}_X$ restricted to $U$, i.e. $e(\tau(\zeta,x)) = u_K(\zeta)\cdot e(x)$.
--
--   This is the step, in the Bosch–Lütkebohmert–Raynaud construction of Néron models by smoothening and gluing of $\omega$-minimal components, which transports a translate landing in a component reading $T$ back into $X$ itself once $T$ is represented by an open-immersion chart into one of the chosen components. It is used by [`NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal`](thm.html#NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_formallySmooth_stalk_of_isOmegaMinimal), where the chart $(c,W,\varepsilon)$ is produced from $\omega$-minimality and the data $(U_1,v)$ from a formal smoothness argument at the stalk of $\eta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep.lean

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

theorem NeronModelInfra.exists_nhds_translation_extension_isOpenImmersion_of_isOpenImmersion_homOfLE_comp_of_isOmegaMinimalRep
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
    (U₁ : (pullback z f).Opens) (hηU₁ : η ∈ U₁) (h₁ : U₁ ≤ U₀)
    (hv : IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v))
    (hyτ : τ₀.1.base ⟨η, hηU⟩ = T.y)
    (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f)
    (hε : IsOpenImmersion ε.1) (hεy : ε.1.base ⟨T.y, hyW⟩ = (D.C c).y)
    (hεchart : (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
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
