-- Prove2me | Theorems.Thm_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
-- name    : NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/53896dc2-3ffa-5fa1-8c83-25858fde78b3
-- title:
--   Order comparison along a chart-compatible morphism of ω-readings
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, let $g_K\colon X_K\to\operatorname{Spec}K$ be smooth of relative dimension $d$, and let $\omega$ be a global section over $\top$ of the $d$-th determinant module `gK.topDifferentials d` of the Kähler module of $g_K$ which is a frame on $\top$, i.e. for every open $W$ of $X_K$ the map $g\mapsto g\cdot\omega|_W$ from $\Gamma(X_K,W)$ to the sections of that module over $W$ is bijective. Let $T$ and $T'$ be two data packages of type `ComponentReading R K gK d ω`, each consisting of a smooth, locally of finite type $f\colon Y\to\operatorname{Spec}R$, an open immersion $e$ of the generic fibre $Y\times_{\operatorname{Spec}R}\operatorname{Spec}K$ into $X_K$ over $\operatorname{Spec}K$, a point $y$ above the closed point of $\operatorname{Spec}R$ which is the only point above the closed point specialising to it, a discrete valuation ring structure on $\mathcal O_{Y,y}$ with compatible $R$-algebra structure and with $K$-algebra structure on $\operatorname{Frac}\mathcal O_{Y,y}$, a basis $b$ of $\Omega_{\mathcal O_{Y,y}/R}$ indexed by $\mathrm{Fin}\,d$, an affine open chart $U\subseteq X_K$ with the attendant compatibilities, and a numerical invariant `n`. Let $W$ be an open of $T.Y$ containing $T.y$ and let $u$ be a morphism from $W$ to $T'.Y$ over $\operatorname{Spec}R$, that is, satisfying $u\;\text{followed by}\;T'.f = W.\iota\;\text{followed by}\;T.f$, and assume the charts agree on generic fibres: the morphism induced by $u$ on generic fibres followed by $T'.e$ equals the morphism induced by $W.\iota$ followed by $T.e$. Assume further that $T'.y$ specialises to $u(T.y)$. Then $T'.n\le T.n$; and if $T.n=T'.n$ then $u(T.y)=T'.y$ and there is an open $W'\subseteq W$ containing $T.y$ such that the inclusion $W'\to W$ followed by $u$ is an open immersion.
--
--   This is the comparison of the order of a top-degree differential form along a chart-compatible morphism between two readings of a component, in the style of Bosch–Lütkebohmert–Raynaud's treatment of minimal models ($\S4.3$): the order cannot drop, and in the case of equality the morphism identifies a neighbourhood of the marked point with an open subscheme of the target around its marked point. It is used in the existence proof for $\omega$-minimal component data, [`NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints`](thm.html#NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints), which underlies the construction of Néron models for Jacobians in the present development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_ComponentReading_n_le_n_and_isOpenImmersion_of_n_eq_of_specializes.lean

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

open CategoryTheory CategoryTheory.Limits Opposite GoodReductionJacobian
open AlgebraicGeometry
open NeronModelInfra

universe u

theorem NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)
    (hgen : T'.y ⤳ u.1.base ⟨T.y, hyW⟩) :
    T'.n ≤ T.n ∧
    (T.n = T'.n → u.1.base ⟨T.y, hyW⟩ = T'.y ∧
      ∃ (W' : T.Y.Opens) (hW' : W' ≤ W), T.y ∈ W' ∧ IsOpenImmersion (T.Y.homOfLE hW' ≫ u.1)) := by sorry
