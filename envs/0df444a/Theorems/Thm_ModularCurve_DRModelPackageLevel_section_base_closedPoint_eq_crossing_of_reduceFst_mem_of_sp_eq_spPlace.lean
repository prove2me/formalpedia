-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_section_base_closedPoint_eq_crossing_of_reduceFst_mem_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.section_base_closedPoint_eq_crossing_of_reduceFst_mem_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/58ecf53e-4e0c-5d48-abad-30272e9d8b7c
-- title:
--   Non-strict inertia-fixed places specialise to crossings
-- statement:
--   Fix a nonzero $N_0$ and a prime $q$ with $q \nmid N_0$, a valuation subring $A$ of $\overline{\mathbf Q}$ with $q$ a nonunit of $A$, and a ring map $\rho$ from the base ring `DRLevel.R q` to $A$ compatible with the structure map to $\overline{\mathbf Q}$; let $\mathfrak P$ be a `DRModelPackageLevel N₀ q hqN`, and let $\kappa =$ `ResidueField A` be of characteristic $q$ and algebraically closed. Given modular polynomial data `data` for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps $\bar\alpha,\bar\beta$ at level $N_0,q$, a fibre model `fm` over $A$ with reduction `residue A` together with its cusp chart, the hypotheses `hfin`, `hinf` that the images under `coeffEmb` of the Igusa chart algebras `chartAlgFin N₀ q`, `chartAlgInf N₀ q` lie in `fm.BFin`, `fm.BInf`, surjectivity of the residue map, modular polynomial data for all divisors of $N_0$ and separability of the reduction of $\Phi$ over `RatFunc κ`, let $P$ be a place specialisation whose map $P.\mathrm{sp}$ is `fm.spPlace`, and let $W$ be a finset of places of `modularFunctionFieldC κ N₀` whose members are exactly the supersingular places `ssPlaces q N₀ κ`. Let $O$ be a discrete valuation domain, $e_O$ an isomorphism of $O$ onto the contraction of $A$ to the fixed field of the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\ \mathbf Q$, $\rho_O$ a structure map on $O$ compatible with $\rho$ through $e_O$, and $\mathrm{to}\kappa : O \to \kappa$ compatible with `residue A` through $e_O$; let $\mathfrak X^{\mathrm{reg}}$ be a `DRResolvedModelPackageLevel` for $\mathfrak P$ over $O$ with residue data $\mathrm{to}\kappa$, and $\sigma_N : W \simeq \mathfrak X^{\mathrm{reg}}.\mathrm{node}$ a bijection pinned so that for each $w \in W$ the place attached by $\mathfrak P.\mathrm{nodeEquiv}$ to the crossing $\mathfrak X^{\mathrm{reg}}.\mathrm{nodeEquiv}(\sigma_N w)$ is $w$. The conclusion: for every place $V$ of `modularFunctionFieldBar (N₀ * q)` with $P.\mathrm{reduceFst}\,V$ (the specialisation under $P.\mathrm{sp}$ of the restriction of $V$ along $\bar\alpha$) lying in $W$, such that $V$ is fixed by the arithmetic Galois action of every element of the inertia subgroup, and such that neither $P.\mathrm{IsStrictFst}\,V$ nor $P.\mathrm{IsStrictSnd}\,V$ holds, the following is true of every section $s$ of the pullback of $\mathfrak P$'s structure morphism `DRLevel.toBase N₀ q` along $\mathrm{Spec}\,\rho_O$ over $\mathrm{Spec}\,O$: if the base change of $s$ to $\overline{\mathbf Q}$, read through the first projection, is the $\overline{\mathbf Q}$-point of the geometric generic fibre corresponding to $V$ under $\mathfrak P.\mathrm{Meta.pointEquivPlace}^{-1}$ followed by $\mathfrak P.\mathrm{eeta}$ and the first projection, then $s$ sends the closed point of $O$ to the image of the crossing $\mathfrak X^{\mathrm{reg}}.\mathrm{nodeEquiv}(\sigma_N\langle P.\mathrm{reduceFst}\,V, hw\rangle)$ under the map given by the first projection of the fibre product of $\mathfrak P.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O)\,0$ and $\mathfrak P.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O)\,1$, followed by $\mathfrak P.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O)\,0$ and the base-change map `DRLevel.bcMap ρO toκ`, as points of the underlying topological spaces.
--
--   This is the node-matching step in the Deligne–Rapoport description of $X_0(N_0q)$ at $q$, whose special fibre is two copies of $X_0(N_0)$ crossing at the supersingular points: a generic point whose reduction is supersingular and which lies strictly on neither branch must specialise to the crossing labelled by that supersingular place. It feeds the construction of a resolved model with its node indexing and the analysis of the supports of the components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_section_base_closedPoint_eq_crossing_of_reduceFst_mem_of_sp_eq_spPlace.lean

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

theorem ModularCurve.DRModelPackageLevel.section_base_closedPoint_eq_crossing_of_reduceFst_mem_of_sp_eq_spPlace

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
    (W : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N₀ (ResidueField ↥A))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackageLevel N₀ q 𝔓 O ρO (ResidueField ↥A) toκ)

    (σN : ↥W ≃ 𝔛reg.node)
    (hσN_pin : ∀ w : ↥W, ((𝔓.nodeEquiv (ResidueField ↥A) (toκ.comp ρO) (𝔛reg.nodeEquiv (σN w)) : ↥(ssPlaces q N₀ (ResidueField ↥A))) : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = (w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))) :
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        s.base (IsLocalRing.closedPoint O) =
          (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)) := by sorry
