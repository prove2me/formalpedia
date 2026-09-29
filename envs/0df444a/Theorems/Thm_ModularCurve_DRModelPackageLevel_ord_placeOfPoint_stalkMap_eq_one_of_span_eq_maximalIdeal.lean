-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
-- name    : ModularCurve.DRModelPackageLevel.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/16f61245-3f1e-5bbe-90d3-9ceabab1cc66
-- title:
--   Crossing coordinates are uniformisers on the two branches
-- statement:
--   Fix $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak{P}$ be a level-$N_0q$ Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for the Igusa-type scheme $X$ over $\operatorname{Spec}(R_q)$. Let $O$ be a discrete valuation domain with a ring map $\rho_O : R_q \to O$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa$ is algebraically closed of characteristic $q$, and let $\mathrm{to}\kappa : O \to \kappa$; assume the fibre `DRLevel.fibre0` of $\mathrm{to}\kappa \circ \rho_O$ (the pullback of `toBase0 N₀ q` along $\operatorname{Spec}$ of that composite) is an integral scheme. Let $x$ be a point of $\mathfrak{X}_O =$ `pullback (DRLevel.toBase N₀ q) (Spec.map ρO)`, let $n$ be a point of the fibre product of the two maps $\mathfrak{P}.\mathrm{comp}\,0$ and $\mathfrak{P}.\mathrm{comp}\,1$ over $\kappa$, and let $P_0, P_1$ be closed points of the curve $C$ of the curve model $\mathfrak{P}.\mathrm{Mfib}$ over $\kappa$ whose images under $\mathfrak{P}.\mathrm{efib}$ are the two projections of $n$, and which both lie over $x$ via $\mathrm{efib}$ followed by $\mathrm{comp}\,i$ followed by `DRLevel.bcMap ρO toκ` ($i = 0, 1$). Assume further that the images of the generic point of `fibre0` under these two composites specialise to $x$. Let $u, v$ be germs in the local ring $\mathcal{O}_{\mathfrak{X}_O, x}$ such that the span of $\{q, u, v\}$ is the maximal ideal, the span of $\{q, u\}$ is the prime obtained by pulling back the maximal ideal along the specialisation map for the first branch, and the span of $\{q, v\}$ is the corresponding prime for the second branch; assume also that the stalk maps of `DRLevel.bcMap ρO toκ` at the two images of $n$ carry the maximal ideal onto the maximal ideal. Then, in the function field of $\mathfrak{P}.\mathrm{Mfib}$ (transported by `ffEquiv.symm`), the function obtained from $v$ by the stalk map at $P_0$ of $\mathrm{efib}$ followed by $\mathrm{comp}\,0$ followed by $\mathrm{bcMap}$ has $\operatorname{ord}$ equal to $1$ at the place attached to $P_0$, and the function obtained from $u$ by the stalk map at $P_1$ of $\mathrm{efib}$ followed by $\mathrm{comp}\,1$ followed by $\mathrm{bcMap}$ has $\operatorname{ord}$ equal to $1$ at the place attached to $P_1$; here $\operatorname{ord}$ is the normalised order $-\log$ of the adic valuation of the place, so each function is a uniformiser at the corresponding point of the branch.
--
--   This is the local form, at level $N_0q$, of the Deligne–Rapoport description of the crossings of the modular curve over a base of residue characteristic $q$: if $u, v$ together with $q$ generate the maximal ideal at a crossing and cut out the two branches, then each of $u, v$ restricts to a uniformiser on the opposite branch. It feeds the extraction of node coordinates and the chart presentation of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
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
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRModelPackageLevel.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)] (toκ : O →+* ResidueField ↥A)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))

    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)))
    (P₀ P₁ : closedPoints ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C)
    (hP₀ : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base P₀.1 = (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)
    (hP₁ : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base P₁.1 = (pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)
    (hx₀ : x = (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base P₀.1)
    (hx₁ : x = (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base P₁.1)
    (hsp₀ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)
    (hsp₁ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)

    (u v : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x)
    (hmax : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), u, v} = IsLocalRing.maximalIdeal ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x))
    (h𝔭₀ : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), u} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom (IsLocalRing.maximalIdeal _))
    (h𝔭₁ : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), v} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _))

    (hunr₀ : Ideal.map ((DRLevel.bcMap ρO toκ).stalkMap ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0).base ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _)
    (hunr₁ : Ideal.map ((DRLevel.bcMap ρO toκ).stalkMap ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1).base ((pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).placeOfPoint P₀).ord
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).ffEquiv.symm (algebraMap _ ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C.functionField
          (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).stalkMap P₀.1).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx₀)).hom.hom v)))) = 1 ∧
    (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).placeOfPoint P₁).ord
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).ffEquiv.symm (algebraMap _ ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C.functionField
          (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).stalkMap P₁.1).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom u)))) = 1 := by sorry
