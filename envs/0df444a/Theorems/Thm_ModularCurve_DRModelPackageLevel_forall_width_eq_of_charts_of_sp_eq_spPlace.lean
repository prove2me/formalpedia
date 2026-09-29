-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_forall_width_eq_of_charts_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.forall_width_eq_of_charts_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/ceabc4e8-5432-5b57-9942-189fa5d59b4d
-- title:
--   Node widths of the resolved model equal place widths
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, together with a ring map $\rho \colon R_q \to A$ compatible with the structure map $R_q \to \overline{\mathbb Q}$, and a Deligne–Rapoport model package $\mathfrak P$ for level $(N_0,q)$; the residue field $\kappa_A$ of $A$ is assumed algebraically closed of characteristic $q$. The data are grouped as follows, all hypotheses being summarised here: modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the Hecke $\bar\alpha$, $\bar\beta$, modular polynomial data for every divisor of $N_0$ with $\Phi$ separable over $\kappa_A(T)$, and surjectivity of the residue map $A \to \kappa_A$; a fibre model $fm$ over $A$ with a cusp chart, whose subrings $B_{\mathrm{fin}}$, $B_\infty$ contain the images under $\mathrm{coeffEmb}$ of the Igusa chart algebras at level $N_0q$; a place specialisation $P$ whose map on places is the specialisation map $fm.\mathrm{spPlace}$ of the fibre model, a prolongation tuple $R$ of $P$ which is a model, satisfies the fixed order law and, on the finite set $W$ of all supersingular places of $X_0(N_0)$ over $\kappa_A$, the regularity and node-value laws and the value-integrality law; a width datum $e$ on places with $e(w) = \mathrm{placeWidthChar}\,q\,N_0\,w$, that is $\mathrm{jWidthChar}_q$ of the value of $j$ at $w$ divided by the ramification of $w$ over the $j$-line, for $w \in W$; a number field $K \subset \overline{\mathbb Q}$, an element $\varpi$ of the coefficient subring $A \cap K$ generating the kernel of reduction, and $e_K \ge 1$, a unit $\varepsilon$ with $q = \varpi^{e_K}\varepsilon$; node coordinates $x_w,y_w$ in the node integers over $K$ at each $w \in W$ with $x_w y_w$ a unit times $\varpi^{e(w)e_K}$, with $(\varpi, x_w, y_w)$ the unique maximal ideal, $(\varpi,x_w)$ and $(\varpi,y_w)$ prime with $y_w$, resp. $x_w$, outside them, Noetherianity of these rings, and the condition that no element is a unit after subtracting a suitable constant; a discrete valuation ring $O$ isomorphic to the pullback of $A$ to the fixed field of the inertia subgroup, with maximal ideal $(q)$, a compatible $\rho_O \colon R_q \to O$ and a map $\mathrm{to}\kappa \colon O \to \kappa_A$ inducing the residue map; a resolved Deligne–Rapoport model package $\mathfrak X_{\mathrm{reg}}$ of $\mathfrak P$ over $O$; a family $Fc$ of ideal sheaf data on the toric resolutions of $uv = q^e$ cutting out, on each standard chart, the coordinate divisors as indicated, and crossing charts $ch$ for $\mathfrak X_{\mathrm{reg}}$ regarded as a ramified resolved package with uniformiser $q$; and a bijection $\sigma_N$ from $W$ to the set of nodes of $\mathfrak X_{\mathrm{reg}}$ such that the supersingular place attached to $\sigma_N(w)$ through the node equivalences of $\mathfrak X_{\mathrm{reg}}$ and $\mathfrak P$ is $w$. The conclusion is that for every $w \in W$ the width $\mathfrak X_{\mathrm{reg}}.\mathrm{width}(\sigma_N(w))$ recorded in the resolved package equals $e(w)$.
--
--   This is the thickness computation of Deligne–Rapoport: the local equation of $X_0(N_0q)$ over an unramified base at a supersingular point of the special fibre is $uv = q^{e}$, with $e$ the width of the corresponding place of $X_0(N_0)$ measured by $\mathrm{placeWidthChar}$. It is used in the construction of a resolved Deligne–Rapoport model package with prescribed node data, and thereby in the analysis of the special fibre entering the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_forall_width_eq_of_charts_of_sp_eq_spPlace.lean

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

theorem ModularCurve.DRModelPackageLevel.forall_width_eq_of_charts_of_sp_eq_spPlace

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ q}

    (fm : CharPModel.FibreModel N₀ A q (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (hfin : ∀ b : IgusaScheme.chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
    (hinf : ∀ b : IgusaScheme.chartAlgInf N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BInf)
    (hred : Function.Surjective (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N₀ → ModularPolynomialData d)
    (hsepΦ : (((dataAll N₀ (dvd_refl N₀)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N₀ data hKr (ResidueField ↥A) (residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace hred dataAll hsepΦ)
    (R : ProlongationTuple P)
    (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N₀ (ResidueField ↥A))
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)

    (e : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) → ℕ) (he : ∀ w ∈ W, e w = placeWidthChar q N₀ w)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict (residue ↥A) K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (cs : ∀ w ∈ W, R.NodeCoordinates K w)
    (hxy : ∀ w (hw : w ∈ W), ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧
        (cs w hw).x * (cs w hw).y = R.nodeConst K w ϖ ^ (e w * eK) * u)
    (hmax : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, (cs w hw).x, (cs w hw).y})
    (hbr : ∀ w (hw : w ∈ W),
        (Ideal.span {R.nodeConst K w ϖ, (cs w hw).x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, (cs w hw).y}).IsPrime ∧
        (cs w hw).y ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).x} ∧ (cs w hw).x ∉ Ideal.span {R.nodeConst K w ϖ, (cs w hw).y})
    (hnoeth : ∀ w ∈ W, IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ w ∈ W, ∀ g : ↥(R.nodeIntegersOver K w),
        ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackageLevel N₀ q 𝔓 O ρO (ResidueField ↥A) toκ)

    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((q : ℕ) : O) e).IdealSheafData) (hF : ∀ (e : ℕ) (i : Fin e) (k' : Fin (e + 1)), (Fc e k').comap (Resolution.ι ((q : ℕ) : O) e i) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((q : ℕ) : O)))).inv.hom
          (if (k' : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((q : ℕ) : O)} else if (k' : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((q : ℕ) : O)}
            else ⊤)))
    (ch : (DRResolvedModelPackageLevelRam.ofUnramified 𝔛reg).DRResolvedModelChartsLevelRam Fc)

    (σN : ↥W ≃ 𝔛reg.node)
    (hσN_pin : ∀ w : ↥W, ((𝔓.nodeEquiv (ResidueField ↥A) (toκ.comp ρO) (𝔛reg.nodeEquiv (σN w)) : ↥(ssPlaces q N₀ (ResidueField ↥A))) : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = (w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))
    :
    ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)) := by sorry
