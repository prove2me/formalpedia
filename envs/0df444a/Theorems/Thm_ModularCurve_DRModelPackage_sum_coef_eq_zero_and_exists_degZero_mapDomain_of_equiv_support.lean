-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_sum_coef_eq_zero_and_exists_degZero_mapDomain_of_equiv_support
-- name    : ModularCurve.DRModelPackage.sum_coef_eq_zero_and_exists_degZero_mapDomain_of_equiv_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7dcd9700-4568-5ff5-a00e-93827da777d2
-- title:
--   Transporting a degree-zero divisor along a level equivalence
-- statement:
--   Let $p$ be a prime and let $\mathfrak{X}$ be a Deligne–Rapoport model package for $p$; among its data is a curve model $\mathfrak{X}.\mathrm{M\eta}$ over $\overline{\mathbb{Q}}$ with function field $\mathrm{modularFunctionFieldBar}\ p$, whose bijection `pointEquivPlace` identifies the sections of $\mathfrak{X}.\mathrm{M\eta}.\mathrm{toBase}$ with the places of that function field. Assume given an isomorphism of additive groups $e_{LT} : \mathrm{JZero}(1\cdot p) \simeq \mathrm{JZero}(p)$, where $\mathrm{JZero}(N)$ is the group of degree-zero divisors of $\mathrm{modularFunctionFieldBar}\ N$ over $\overline{\mathbb{Q}}$ modulo principal ones, a bijection $e_{Pl}$ between the place sets at levels $1\cdot p$ and $p$, and the compatibility $h_{e_{Pl}}$: whenever a degree-zero divisor $D_2$ at level $p$ equals $\mathrm{Finsupp.mapDomain}\ e_{Pl}\ D_1$ for a degree-zero divisor $D_1$ at level $1\cdot p$, then $e_{LT}$ sends the class of $D_1$ to the class of $D_2$. Let $D_0$ be a divisor at level $1\cdot p$ in the kernel of the degree homomorphism, let $m\in\mathbb{N}$, let $\mathrm{idx}$ be a bijection from $\mathrm{Fin}\ m$ onto the support of $D_0$, and let $\mathrm{coef} : \mathrm{Fin}\ m \to \mathbb{Z}$ satisfy $\mathrm{coef}\ j = D_0(\mathrm{idx}\ j)$. The conclusion is twofold: $\sum_j \mathrm{coef}\ j = 0$, and there is a degree-zero divisor $D_x$ at level $p$ whose underlying finitely supported function is $\sum_j \mathrm{Finsupp.single}$ at the place $\mathfrak{X}.\mathrm{M\eta}.\mathrm{pointEquivPlace}(\mathfrak{X}.\mathrm{M\eta}.\mathrm{pointEquivPlace}^{-1}(e_{Pl}(\mathrm{idx}\ j)))$ with value $\mathrm{coef}\ j$ — the round trip through points being the identity, this is just the push-forward $\mathrm{mapDomain}\ e_{Pl}\ D_0$ — and such that $e_{LT}$ carries the class of $D_0$ to the class of $D_x$.
--
--   This is the bookkeeping step that rewrites a degree-zero divisor class at level $1\cdot p$ as an explicitly enumerated divisor at level $p$, phrased through the point–place dictionary of the Deligne–Rapoport model package, so that the coefficients may afterwards be attached to honest sections of the model. It is used in the construction of a scheme morphism over the base from a vanishing Abel–Jacobi condition, in [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_sum_coef_eq_zero_and_exists_degZero_mapDomain_of_equiv_support.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 800000 in

theorem ModularCurve.DRModelPackage.sum_coef_eq_zero_and_exists_degZero_mapDomain_of_equiv_support
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (eLT : JZero (1 * p) ≃+ JZero p)
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl : ∀ (D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
        (D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)))),
      (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) =
          Finsupp.mapDomain ePl (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
      eLT (Pic0.mk D₁) = Pic0.mk D₂)
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
    (m : ℕ) (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support))
    (coef : Fin m → ℤ)
    (hcoef : ∀ j, coef j = (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
      (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))) :
    (∑ j, coef j) = 0 ∧
    ∃ Dx : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p))),
      (Dx : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
        ∑ j, Finsupp.single (𝔛.Mη.pointEquivPlace ((𝔛.Mη.pointEquivPlace).symm
          (ePl (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))))) (coef j) ∧
      eLT (Pic0.mk D₀) = Pic0.mk Dx := by sorry
