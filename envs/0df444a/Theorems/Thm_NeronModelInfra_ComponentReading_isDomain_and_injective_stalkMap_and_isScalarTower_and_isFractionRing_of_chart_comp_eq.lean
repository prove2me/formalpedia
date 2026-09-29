-- Prove2me | Theorems.Thm_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
-- name    : NeronModelInfra.ComponentReading.isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/9a26f24c-3061-5882-8758-075220fc0e82
-- title:
--   Stalk birationality along a chart-compatible morphism of readings
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), $K$ a field which is an $R$-algebra realising $K$ as the fraction field of $R$, let $g_K : X_K \to \operatorname{Spec} K$ be smooth of relative dimension $d$, and let $\omega$ be a global section of $g_K$'s $d$-th top differentials, i.e. of the $d$-th determinant of the sheafified Kähler module of $g_K$. Let $T$ and $T'$ be two elements of `ComponentReading R K gK d ω`; such a datum consists of a scheme $Y$ with a smooth, locally of finite type morphism $f : Y \to \operatorname{Spec} R$, a morphism $e$ from the generic fibre $Y \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $X_K$ over $\operatorname{Spec} K$ which is an open immersion, a point $y$ with $f(y)$ the closed point of $\operatorname{Spec} R$ and maximal in the sense that any $y'$ specialising to $y$ and lying over the closed point equals $y$, together with the facts that $\mathcal O_{Y,y}$ is a domain and a discrete valuation ring, an $R$-algebra structure on $\mathcal O_{Y,y}$ compatible with $f$ via `fromSpecStalk`, a $K$-algebra structure on $\operatorname{Frac}\mathcal O_{Y,y}$ forming a scalar tower over $R$, a basis of $\Omega_{\mathcal O_{Y,y}/R}$ indexed by $\operatorname{Fin} d$, an affine open $U \subseteq X_K$ with an algebra structure of $\Gamma(X_K,U)$ on $\operatorname{Frac}\mathcal O_{Y,y}$, and further fields relating these data to $\omega$, summarised here. Let $W$ be an open subscheme of $T.Y$ with $T.y \in W$, and let $u : W \to T'.Y$ satisfy $u$ followed by $T'.f$ equal to the inclusion $W \hookrightarrow T.Y$ followed by $T.f$. Assume the charts agree on generic fibres: the generic fibre restriction of $u$ followed by $T'.e$ equals the generic fibre restriction of the inclusion $W \hookrightarrow T.Y$ followed by $T.e$. Write $O := \mathcal O_{T.Y,\,T.y}$ with the $R$-algebra structure carried by $T$, $y_1 := u(T.y)$, $O' := \mathcal O_{T'.Y,\,y_1}$ with the $R$-algebra structure `stalkAlgebra T'.f y₁`, and let $\varphi : O' \to O$ be the stalk map of $u$ at $T.y$ followed by the canonical identification of the stalk of $W$ with that of $T.Y$. Then $O'$ is a domain, $\varphi$ is injective, $R \to O' \xrightarrow{\varphi} O$ is a scalar tower (the $R$-algebra structures are compatible), and $\varphi$ followed by $O \to \operatorname{Frac} O$ exhibits $\operatorname{Frac} O$ as a fraction field of $O'$.
--
--   This is the birationality step in the comparison of two $\omega$-readings of a smooth $R$-scheme, in the style of the local arguments used for Néron models: agreement of the two charts on generic fibres forces the stalk map at the distinguished point to be a localisation onto a common fraction field. It is used in the proof of [`NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes`](thm.html#NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes), where minimality of the readings is compared and the open-immersion property is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
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

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.ComponentReading.isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)}
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    letI := T.algebra
    letI φ : T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩) ⟶ T.Y.presheaf.stalk T.y :=
      u.1.stalkMap ⟨T.y, hyW⟩ ≫ (W.stalkIso ⟨T.y, hyW⟩).hom
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) := φ.hom.toAlgebra
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) :=
      ((algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))).comp φ.hom).toAlgebra
    letI : Algebra R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) := stalkAlgebra T'.f (u.1.base ⟨T.y, hyW⟩)
    IsDomain (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) ∧
      Function.Injective φ.hom ∧
      IsScalarTower R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) ∧
      IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) := by sorry
