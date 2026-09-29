-- Prove2me | Theorems.Thm_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes
-- name    : NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/188ed6ce-9c62-57d0-b1ab-cd438ff64e63
-- title:
--   Existence of an ω-reading at a maximal special-fibre point
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $g_K \colon X_K \to \operatorname{Spec} K$ be smooth of relative dimension $d$, and let $\omega \in \Gamma(X_K, \top)$ be a global section of the $d$-th determinant `gK.topDifferentials d` of the relative Kähler sheaf of $g_K$ which is a frame on $\top$, i.e. for every open $W \subseteq X_K$ the map $g \mapsto g \cdot \omega|_W$ from $\Gamma(X_K, W)$ to the sections of `gK.topDifferentials d` over $W$ is bijective. Let $f \colon Y \to \operatorname{Spec} R$ be smooth and locally of finite type, let $e$ be a morphism from the generic fibre $Y \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (taken with its second projection) to $X_K$ commuting with the structure maps to $\operatorname{Spec} K$, whose underlying morphism is an open immersion, and let $y \in Y$ be a point lying over the closed point of $R$ such that every point $y'$ specialising to $y$ and lying over the closed point equals $y$. Then, writing $\mathcal O = \mathcal O_{Y,y}$ and $F = \operatorname{Frac}(\mathcal O)$, the statement asserts the existence of: proofs that $\mathcal O$ is a domain and a discrete valuation ring; an $R$-algebra structure on $\mathcal O$ for which `Y.fromSpecStalk y` followed by $f$ is $\operatorname{Spec}$ of its structure map; a $K$-algebra structure on $F$ making $R \to K \to F$ a scalar tower; a basis $b$ of $\Omega_{\mathcal O/R}$ indexed by `Fin d`; an affine open $U \subseteq X_K$ together with a $\Gamma(X_K,U)$-algebra structure on $F$ compatible with the $K$-algebra structure on $\Gamma(X_K,U)$ coming from $g_K$, such that $\operatorname{Spec}$ of $\Gamma(X_K,U) \to F$ followed by the canonical morphism $\operatorname{Spec} \Gamma(X_K,U) \to X_K$ equals the $F$-point of $X_K$ obtained from the $\mathcal O$-point `Y.fromSpecStalk y` of $Y$ by passing to the generic fibre and composing with $e$; an element $\omega_U$ of $\bigwedge^d_{\Gamma(X_K,U)}$ of the Kähler presheaf at $U$ whose image under `gK.topToSections d U` is the restriction of $\omega$ to $U$; and a scalar $a \in F$ with $a \neq 0$ such that the image of $\omega_U$ in $\bigwedge^d_F \Omega_{F/K}$ equals $a$ times the image of $db_1 \wedge \dots \wedge db_d$ under the corresponding base-change map `TopFormOrder.topFormMap R K` $\mathcal O\, F\, d$.
--
--   This is the local input to the computation of the order of a global $d$-form along a maximal point of the special fibre of a smooth model, as in the theory of weak Néron models: it produces all the data needed to compare $\omega$ with a basis of $\Omega_{\mathcal O_{Y,y}/R}$ inside $\bigwedge^d_F \Omega_{F/K}$. It is used in the construction of minimal component data and in the verification of $\omega$-minimality for extensions of translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_componentReading_data_of_smooth_of_forall_specializes.lean

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
open NeronModelInfra
open GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsOpenImmersion e.1]
    (y : Y) (hy : f.base y = IsLocalRing.closedPoint R)
    (hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y) :
    ∃ (_ : IsDomain (Y.presheaf.stalk y)) (_ : IsDiscreteValuationRing (Y.presheaf.stalk y))
      (algebra : Algebra R (Y.presheaf.stalk y))
      (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))))
      (algebraK : Algebra K (FractionRing (Y.presheaf.stalk y)))
      (_ : IsScalarTower R K (FractionRing (Y.presheaf.stalk y)))
      (b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R]))
      (U : XK.Opens) (hU : IsAffineOpen U)
      (algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))
      (_ : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
        (schemeHomOverComp
          (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
            (⟨Y.fromSpecStalk y, halg⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
          e).1)
      (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
      (_ : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
      (a : FractionRing (Y.presheaf.stalk y)),
      (letI := gK.sectionsAlgebra U;
        TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
          a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
            (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)) ∧
      a ≠ 0 := by sorry
