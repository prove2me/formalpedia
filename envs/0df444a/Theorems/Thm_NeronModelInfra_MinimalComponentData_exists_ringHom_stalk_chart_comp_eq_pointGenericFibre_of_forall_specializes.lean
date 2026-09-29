-- Prove2me | Theorems.Thm_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
-- name    : NeronModelInfra.MinimalComponentData.exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/254d4ddc-ac1d-5672-bbfd-3f949a5e5df9
-- title:
--   A maximal special point of a glued model comes from one component
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, let $g_K\colon X_K \to \operatorname{Spec} K$ be smooth, separated, locally of finite type and quasi-compact of relative dimension $d$, let $\omega$ be a global section of the $d$-th determinant of the sheafified Kähler differentials of $g_K$, and let $D$ be a `MinimalComponentData` for $(R,K,g_K,d,\omega)$: a finite nonempty index type $D.\iota$ together with component readings $D.C\,c$, each consisting of a smooth, locally of finite type, separated, quasi-compact $R$-scheme $(D.C\,c).f\colon Y_c \to \operatorname{Spec} R$ whose generic fibre is identified with $X_K$ by an isomorphism $(D.C\,c).e$ over $g_K$, a point $y_c$ over the closed point of $R$ maximal for specialisation there and generic in the special fibre, a discrete valuation stalk $\mathcal O_{Y_c,y_c}$ with compatible $R$-algebra structure, a basis of its module of differentials, and an affine open $U_c \subseteq X_K$ with an algebra map $\Gamma(X_K,U_c) \to \operatorname{Frac}\mathcal O_{Y_c,y_c}$, the readings being pairwise inequivalent. Let $f\colon X \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, let $e$ be a morphism from the generic fibre $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $g_K$ with $e$ an isomorphism, and for each $c$ let $V_c \subseteq Y_c$ be open with $j_c\colon V_c \to X$ a morphism over $R$. Assume $y_c \in V_c$; every point of $Y_c$ not lying over the closed point of $R$ lies in $V_c$; each $j_c$ is an open immersion; the generic-fibre restriction of $j_c$ followed by $e$ agrees with the generic-fibre restriction of $V_c \hookrightarrow Y_c$ followed by $(D.C\,c).e$; and the images of the $j_c$ cover $X$. Let $\xi \in X$ lie over the closed point of $R$ and be maximal in the sense that any $y$ specialising to $\xi$ and lying over the closed point equals $\xi$, let $\mathcal O_{X,\xi}$ carry an $R$-algebra structure compatible with $f$ via $X.\mathrm{fromSpecStalk}\,\xi$, and let $F$ be a field that is an algebra over $\mathcal O_{X,\xi}$, over $R$ and over $K$, with the two scalar towers $R \to \mathcal O_{X,\xi} \to F$ and $R \to K \to F$, such that $\mathcal O_{X,\xi} \to F$ is injective. Then there are an index $c$ and a ring homomorphism $\varphi\colon \mathcal O_{Y_c,y_c} \to \mathcal O_{X,\xi}$ such that $j_c(y_c) = \xi$, $\varphi$ is bijective, local, and compatible with the $R$-algebra structures, together with an algebra structure on $F$ over $\operatorname{Frac}\mathcal O_{Y_c,y_c}$ extending $\mathcal O_{Y_c,y_c} \xrightarrow{\varphi} \mathcal O_{X,\xi} \to F$ and compatible with $K \to \operatorname{Frac}\mathcal O_{Y_c,y_c}$, for which the following holds: giving $F$ the $\Gamma(X_K,U_c)$-algebra structure obtained by composing $\Gamma(X_K,U_c) \to \operatorname{Frac}\mathcal O_{Y_c,y_c}$ with $\operatorname{Frac}\mathcal O_{Y_c,y_c} \to F$, the morphism $\operatorname{Spec} F \to \operatorname{Spec}\Gamma(X_K,U_c)$ followed by the canonical morphism $\operatorname{Spec}\Gamma(X_K,U_c) \to X_K$ of the affine open $U_c$ equals the $F$-point of $X_K$ obtained from the generic-fibre point attached to $X.\mathrm{fromSpecStalk}\,\xi$ followed by $e$.
--
--   This is the bookkeeping step behind Bosch–Lütkebohmert–Raynaud 4.3, Proposition 4: on a model glued from finitely many component readings, a point of the special fibre maximal for specialisation is the distinguished point $y_c$ of exactly one member, its local ring is identified with $\mathcal O_{Y_c,y_c}$ by a local isomorphism over $R$, and the resulting $F$-point of the generic fibre is read off on that member's affine chart $U_c$. It is used in the computation of the order of vanishing of $\omega$ at a maximal special point of the glued model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_MinimalComponentData_exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes.lean

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

theorem NeronModelInfra.MinimalComponentData.exists_ringHom_stalk_chart_comp_eq_pointGenericFibre_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (D : MinimalComponentData R K gK d ω)
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
    (ξ : ↥X) (hξ : f.base ξ = IsLocalRing.closedPoint R)
    (hξmax : ∀ y : ↥X, y ⤳ ξ → f.base y = IsLocalRing.closedPoint R → y = ξ)
    [Algebra R (X.presheaf.stalk ξ)]
    (halgX : X.fromSpecStalk ξ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ))))
    (F : Type u) [Field F] [Algebra (X.presheaf.stalk ξ) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (X.presheaf.stalk ξ) F] [IsScalarTower R K F]
    (hinj : Function.Injective (algebraMap (X.presheaf.stalk ξ) F)) :
    ∃ (c : D.ι) (φ : ((D.C c).Y.presheaf.stalk (D.C c).y) →+* (X.presheaf.stalk ξ))
      (_ : (j c).1.base ⟨(D.C c).y, hyV c⟩ = ξ)
      (_ : Function.Bijective φ) (_ : IsLocalHom φ)
      (_ : letI := (D.C c).algebra; φ.comp (algebraMap R ((D.C c).Y.presheaf.stalk (D.C c).y)) = algebraMap R (X.presheaf.stalk ξ))
      (algF : Algebra (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : letI : Algebra ((D.C c).Y.presheaf.stalk (D.C c).y) F := ((algebraMap (X.presheaf.stalk ξ) F).comp φ).toAlgebra
           IsScalarTower ((D.C c).Y.presheaf.stalk (D.C c).y) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F)
      (_ : letI := (D.C c).algebraK; IsScalarTower K (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F),
      letI := gK.sectionsAlgebra (D.C c).U
      letI := (D.C c).algebraU
      letI : Algebra Γ(XK, (D.C c).U) F :=
        ((algebraMap (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)) F).comp (algebraMap Γ(XK, (D.C c).U) (FractionRing ((D.C c).Y.presheaf.stalk (D.C c).y)))).toAlgebra
      Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, (D.C c).U) F)) ≫ (D.C c).hU.fromSpec =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨X.fromSpecStalk ξ, halgX⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.stalk ξ)))) f))
          e).1 := by sorry
