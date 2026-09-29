-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_swap_forall_isStrict_section_mem_range_comp_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.exists_swap_forall_isStrict_section_mem_range_comp_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/52bfd6b4-3247-5412-8a33-5676ba7b683b
-- title:
--   Strict places specialise into one labelled component
-- statement:
--   Fix $N_0\neq 0$ and a prime $q$ with $q\nmid N_0$, a valuation subring $A$ of $\overline{\mathbf Q}$ in which $q$ is a nonunit, and a ring map $\rho\colon R_q\to A$ whose composite with the inclusion $A\hookrightarrow\overline{\mathbf Q}$ is the structural map. Let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for the Igusa-type scheme $X$ of level $N_0q$ over $R_q$ (bundling properness, flatness, integrality and local finite presentation of `DRLevel.toBase N₀ q`, normality on affine opens, a curve model `Meta` of $\overline{\mathbf Q}\cdot$`modularFunctionFieldBar (N₀ * q)` together with a Galois-compatible isomorphism `eeta` onto the geometric generic fibre, cusp pinnings, smoothness and geometric integrality of the generic fibre, and further data). Assume the residue field $\kappa=$`ResidueField ↥A` has characteristic $q$ and is algebraically closed. Given modular polynomial data `data` at $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha,h\beta$ for the two degeneracy embeddings at level $N_0$ into level $N_0q$, a fibre model `fm` over $(A,\kappa,\mathrm{res})$ with a cusp chart `cc`, the hypotheses `hfin`, `hinf` that every element of `IgusaScheme.chartAlgFin N₀ q`, respectively `chartAlgInf N₀ q`, lies in `fm.BFin`, respectively `fm.BInf`, after transport by `coeffEmb`, surjectivity `hred` of the residue map, modular polynomial data `dataAll d` for every nonzero divisor $d\mid N_0$ and separability `hsepΦ` of the reduction of $\Phi$ at level $N_0$ over `RatFunc κ`, let $P$ be a place specialisation `PlaceSpecialization A q N₀ data hKr κ (residue ↥A) hα hβ` pinned by $P.\mathrm{sp}=$`fm.spPlace hred dataAll hsepΦ`. Let further $O$ be a discrete valuation domain, $e_O$ a ring isomorphism of $O$ with the valuation ring induced by $A$ on the fixed field of `A.inertiaSubgroupIn ℚ`, $\rho_O\colon R_q\to O$ a lift of the structural map through $e_O$, and $\mathrm{to}\kappa\colon O\to\kappa$ the induced reduction, pinned pointwise by `htoκ`. Then there is a single Boolean `swap` such that for every place $V$ of `modularFunctionFieldBar (N₀ * q)` over $\overline{\mathbf Q}$ fixed by the arithmetic Galois action of every $\sigma\in$`A.inertiaSubgroupIn ℚ`, and every $s\colon \operatorname{Spec}O\to X\times_{R_q}O$ which is a section of the projection to $\operatorname{Spec}O$ and whose base change to $\overline{\mathbf Q}$ is the geometric point `(𝔓.Meta.pointEquivPlace).symm V` transported by `𝔓.eeta`: if $P.\mathrm{IsStrictFst}\,V$ holds, that is $\mathrm{Frob}(P.\mathrm{reduceFst}\,V)=P.\mathrm{reduceSnd}\,V$ and $\mathrm{Frob}^2(P.\mathrm{reduceFst}\,V)\neq P.\mathrm{reduceFst}\,V$, then the image of the closed point of $O$ under $s$ lies in the range of the underlying map of the component morphism $\mathfrak P.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa\circ\rho_O)\,i$ followed by `DRLevel.bcMap ρO toκ` for $i=1$ if `swap` and $i=0$ otherwise, and not in the range for the other index; and symmetrically, if $P.\mathrm{IsStrictSnd}\,V$ holds, the two indices are exchanged.
--
--   This is the branch-matching step for the Deligne–Rapoport model of $X_0(N_0q)$ at $q$: the special fibre carries two labelled copies of the level-$N_0$ curve, and a place strict of the first kind, respectively of the second kind, forces any integral section through it to reduce into one copy and off the other, with an orientation bit independent of the place and of the section. It feeds the construction of the resolved model package and its node coordinates, via [`ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace`](thm.html#ModularCurve.DRModelPackageLevel.exists_dRResolvedModelPackageLevel_nodeEquiv_swap_nodeCoordinates_of_surjective_of_sp_eq_spPlace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_swap_forall_isStrict_section_mem_range_comp_of_sp_eq_spPlace.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_swap_forall_isStrict_section_mem_range_comp_of_sp_eq_spPlace

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
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩) :
    ∃ swap : Bool, ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 else 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base) := by sorry
