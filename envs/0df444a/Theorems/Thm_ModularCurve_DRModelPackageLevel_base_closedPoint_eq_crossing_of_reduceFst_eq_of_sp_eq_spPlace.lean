-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_base_closedPoint_eq_crossing_of_reduceFst_eq_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.base_closedPoint_eq_crossing_of_reduceFst_eq_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/baa0e398-9ba9-5a41-bc3e-c56269f51854
-- title:
--   A-points above supersingular places specialise to the crossing
-- statement:
--   Fix a positive integer $N_0$ and a prime $q$ with $q \nmid N_0$, and let $A$ be a valuation subring of $\overline{\mathbf Q}$ lying over $q$ in the sense that $q$ is a non-unit of $A$, equipped with a ring map $\rho : \mathtt{DRLevel.R}\,q \to A$ compatible with the structure map to $\overline{\mathbf Q}$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ q hqN`. The residue field $\kappa = \mathrm{ResidueField}\,A$ is assumed of characteristic $q$ and algebraically closed, and the reduction $A \to \kappa$ surjective. Further data: modular polynomial data `data` at $q$ satisfying the Kronecker congruence `hKr`; integrality of the two degeneracy maps $\bar\alpha$, $\bar\beta$ at level $(N_0,q)$; a fibre model `fm` of level $N_0$ over $A$ with residue field $\kappa$ together with a cusp chart `cc`, whose subrings `fm.BFin`, `fm.BInf` are assumed to contain the images under coefficientwise base change of the Igusa chart algebras $\mathtt{chartAlgFin}\,N_0\,q$ and $\mathtt{chartAlgInf}\,N_0\,q$; modular polynomial data `dataAll d` for every divisor $d \mid N_0$, with the mod-$q$ reduction of $\Phi$ at level $N_0$ separable over $\mathrm{RatFunc}\,\kappa$; and a place specialisation $P$ whose specialisation map `P.sp` coincides with `fm.spPlace hred dataAll hsepΦ`. On the base side, $O$ is a discrete valuation domain identified by a ring isomorphism `eO` with the intersection of $A$ with the inertia fixed field $\overline{\mathbf Q}^{I_A}$, carrying $\rho_O : \mathtt{DRLevel.R}\,q \to O$, a reduction $\mathrm{to}\kappa : O \to \kappa$ and an inclusion $\mathrm{incl}_O : O \to A$, all compatible with $\rho$, with $A.\mathrm{subtype}$ and with the residue map as stated. Finally $w$ is a place of $\mathtt{modularFunctionFieldC}\,\kappa\,N_0$ lying in $\mathtt{ssPlaces}\,q\,N_0\,\kappa$, i.e. satisfying `IsSupersingularPlace q N₀ κ`. The conclusion: for every place $V$ of $\mathtt{modularFunctionFieldBar}\,(N_0 q)$ with $P.\mathrm{reduceFst}\,V = w$, that is with `P.sp` of the restriction of $V$ along $\bar\alpha$ equal to $w$, and every morphism $s_A : \operatorname{Spec} A \to \mathtt{DRLevel.toBase}\,N_0\,q \times_{\operatorname{Spec}\mathtt{R}\,q} \operatorname{Spec} O$ whose second projection is $\operatorname{Spec}$ of $\mathrm{incl}_O$ and whose restriction along $\operatorname{Spec}$ of $A \hookrightarrow \overline{\mathbf Q}$, followed by the first projection, is the $\overline{\mathbf Q}$-point $(\mathfrak P.\mathrm{Meta}.\mathrm{pointEquivPlace})^{-1}(V)$ followed by $\mathfrak P.\mathtt{eeta}$ and the first projection, the image of the closed point of $A$ under the underlying map of $s_A$ equals the image of $(\mathfrak P.\mathtt{nodeEquiv}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O))^{-1}\langle w, hw\rangle$ under the map of topological spaces induced by the first projection of the pair $\mathfrak P.\mathtt{comp}\,\kappa\,(\mathrm{to}\kappa\circ\rho_O)\,0$, $\mathfrak P.\mathtt{comp}\,\kappa\,(\mathrm{to}\kappa\circ\rho_O)\,1$, followed by $\mathfrak P.\mathtt{comp}\,\kappa\,(\mathrm{to}\kappa\circ\rho_O)\,0$ and then by $\mathtt{DRLevel.bcMap}\,\rho_O\,\mathrm{to}\kappa$.
--
--   This is the $A$-valued-point form of the Deligne–Rapoport description of the fibre at $q$ of the model of $X_0(N_0q)$ over $\mathbf Z_{(q)}$ base changed to the unramified ring $O$: a section whose generic point is the point attached to a place $V$ of $\overline{\mathbf Q}(X_0(N_0q))$ whose first reduction is a supersingular place $w$ has its closed point at the crossing of the two copies of $X_0(N_0)_{\kappa}$ labelled by $w$ through the package's node parametrisation, with no inertia or strictness hypothesis on $V$. It is used by [`ModularCurve.DRModelPackageLevel.mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq`](thm.html#ModularCurve.DRModelPackageLevel.mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq) in the analysis of the local rings at the nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_base_closedPoint_eq_crossing_of_reduceFst_eq_of_sp_eq_spPlace.lean

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
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRModelPackageLevel.base_closedPoint_eq_crossing_of_reduceFst_eq_of_sp_eq_spPlace

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

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (inclO : O →+* ↥A)
    (hinclO : A.subtype.comp inclO = (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))

    (w : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) (hw : w ∈ ssPlaces q N₀ (ResidueField ↥A)) :
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))), P.reduceFst V = w →
      ∀ sA : Spec (CommRingCat.of ↥A) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        sA ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = Spec.map (CommRingCat.ofHom inclO) →
        Spec.map (CommRingCat.ofHom A.subtype) ≫ sA ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        sA.base (IsLocalRing.closedPoint ↥A) =
          (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base ((𝔓.nodeEquiv (ResidueField ↥A) (toκ.comp ρO)).symm ⟨w, hw⟩) := by sorry
