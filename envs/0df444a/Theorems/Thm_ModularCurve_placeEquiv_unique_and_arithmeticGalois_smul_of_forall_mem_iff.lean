-- Prove2me | Theorems.Thm_ModularCurve_placeEquiv_unique_and_arithmeticGalois_smul_of_forall_mem_iff
-- name    : ModularCurve.placeEquiv_unique_and_arithmeticGalois_smul_of_forall_mem_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/445437c3-7b4b-5d79-9f90-b087f340d515
-- title:
--   Uniqueness and Galois equivariance of the place transport 1· p → p
-- statement:
--   Let $p$ be a prime. For a natural number $N$, write $\overline{F}_N$ for `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$, inside $\overline{\mathbb Q}$-Laurent series, of the intermediate field `modularFunctionFieldFull N` of $\mathbb{Q}((q))$ generated over $\mathbb Q$ by the divisor expansions of level $N$; a `Place` of $\overline{F}_N$ over $\overline{\mathbb Q}$ is a valuation subring of $\overline{F}_N$ containing the image of $\overline{\mathbb Q}$, different from the whole field, and whose underlying ring is a principal ideal ring, and `evalAt f` is the value in $\overline{\mathbb Q}$ obtained by taking the residue of $f$ when $f$ is integral at the place (and $0$ otherwise). Let $e$ be a bijection from the places of $\overline{F}_{1\cdot p}$ to the places of $\overline{F}_p$ such that for every place $V$ and all $f \in \overline{F}_{1\cdot p}$, $f' \in \overline{F}_p$ having the same underlying Laurent series, $f$ lies in the valuation subring of $V$ if and only if $f'$ lies in that of $e(V)$, and $V$ and $e(V)$ assign the same value to $f$ and $f'$. The conclusion is twofold: first, any bijection $e'$ with the same property equals $e$; second, for every $\sigma \in \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ and every place $V$ of $\overline{F}_{1\cdot p}$ one has $e(\sigma \cdot V) = \sigma \cdot e(V)$, where $\sigma$ acts through `arithmeticGalois`, the semilinear automorphism applying $\sigma$ coefficientwise to Laurent series.
--
--   This pins down the transport of places along the equality of levels $1\cdot p = p$: the function-level normalisation (agreement of integrality and of values on functions with equal $q$-expansions) admits at most one such bijection, and that bijection automatically commutes with the arithmetic Galois action. It is used in the construction of the Deligne–Rapoport model package, where the transport appears in the statement about germs of $j$ and specialisation into the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_placeEquiv_unique_and_arithmeticGalois_smul_of_forall_mem_iff.lean

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
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_X0MqResolvedTable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization
set_option maxHeartbeats 400000 in

theorem ModularCurve.placeEquiv_unique_and_arithmeticGalois_smul_of_forall_mem_iff
    (p : ℕ) [Fact p.Prime]
    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f') :
    (∀ ePl' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p),
      (∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl' V).toValuationSubring) ∧ V.evalAt f = (ePl' V).evalAt f') → ePl' = ePl) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      ePl (arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V) = arithmeticGalois (modularFunctionFieldFull p) σ • ePl V) := by sorry
