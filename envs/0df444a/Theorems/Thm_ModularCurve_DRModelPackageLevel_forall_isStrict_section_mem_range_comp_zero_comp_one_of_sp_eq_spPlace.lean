-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_forall_isStrict_section_mem_range_comp_zero_comp_one_of_sp_eq_spPlace
-- name    : ModularCurve.DRModelPackageLevel.forall_isStrict_section_mem_range_comp_zero_comp_one_of_sp_eq_spPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/28830643-8107-5dbd-b869-03247f904870
-- title:
--   Strict places orient sections onto the two special-fibre components
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, and a ring map $\rho : \mathtt{DRLevel.R}\,q \to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the structure map; let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN`, and assume the residue field $\kappa$ of $A$ has characteristic $q$ and is algebraically closed. Further data: modular polynomial data `data` at level $q$ satisfying the Kronecker congruence $\overline{\Phi} = (X^q - Y)(X - Y^q)$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy embeddings $\overline{\mathbb Q}(X_0(N_0)) \to \overline{\mathbb Q}(X_0(N_0q))$, a fibre model $fm$ at level $N_0$ over $A$ with residue map $\kappa$, a cusp chart `cc` for it, the hypotheses that the coefficientwise images of the Igusa chart algebras `chartAlgFin N₀ q` and `chartAlgInf N₀ q` lie in $fm.\mathtt{BFin}$ and $fm.\mathtt{BInf}$, surjectivity of the residue map of $A$, modular polynomial data `dataAll` for every divisor of $N_0$ with the level-$N_0$ polynomial separable over $\kappa(T)$ after reduction, and a place specialisation $P$ at $A$ into $\kappa$ with $P.\mathtt{sp} = fm.\mathtt{spPlace}$. Finally, $O$ is a discrete valuation domain identified by a ring isomorphism $e_O$ with the valuation subring $A \cap \overline{\mathbb Q}^{I}$ cut out on the fixed field of the inertia subgroup `A.inertiaSubgroupIn ℚ`, carrying $\rho_O : \mathtt{DRLevel.R}\,q \to O$ whose composite to $\overline{\mathbb Q}$ is the structure map, and $\mathrm{to}\kappa : O \to \kappa$ the induced residue map. The assertion: for every place $V$ of $\overline{\mathbb Q}$ in the base-changed modular function field at level $N_0 q$ which is fixed by the arithmetic Galois action of every element of `A.inertiaSubgroupIn ℚ`, and every section $s$ of the pullback of $\mathtt{toBase}\,N_0\,q$ along $\operatorname{Spec} \rho_O$ over $\operatorname{Spec} O$, such that $\operatorname{Spec}$ of the map $O \to \overline{\mathbb Q}$ followed by $s$ followed by `pullback.fst` is the $\overline{\mathbb Q}$-point $(\mathfrak P.\mathtt{Meta.pointEquivPlace})^{-1}(V)$ followed by $\mathfrak P.\mathtt{eeta}$ followed by `pullback.fst`, the following hold. If $P.\mathtt{IsStrictFst}\,V$, that is $\mathrm{Frob}(P.\mathtt{reduceFst}\,V) = P.\mathtt{reduceSnd}\,V$ and $\mathrm{Frob}^2(P.\mathtt{reduceFst}\,V) \neq P.\mathtt{reduceFst}\,V$ for the geometric-level Frobenius on places of $\kappa(X_0(N_0))$, then the image of the closed point of $O$ under the underlying map of $s$ lies in the range of the underlying map of $\mathfrak P.\mathtt{comp}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O)\,0$ followed by `DRLevel.bcMap ρO toκ`, and not in the corresponding range for index $1$; and if $P.\mathtt{IsStrictSnd}\,V$, namely $P.\mathtt{reduceFst}\,V = \mathrm{Frob}(P.\mathtt{reduceSnd}\,V)$ with $\mathrm{Frob}^2(P.\mathtt{reduceSnd}\,V) \neq P.\mathtt{reduceSnd}\,V$, the two memberships are interchanged.
--
--   This records, in the Deligne–Rapoport model of $X_0(N_0q)$ over $\mathbb Z_{(q)}$, which of the two components of the geometric special fibre at $q$ receives the reduction of an inertia-invariant point of the generic fibre, the orientation being fixed by the package's indexing of the components by $0$ and $1$. It feeds the analysis of the nodes of the special fibre and the resulting description of the component group, via [`ModularCurve.DRModelPackageLevel.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_charts_of_sp_eq_spPlace`](thm.html#ModularCurve.DRModelPackageLevel.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_charts_of_sp_eq_spPlace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_forall_isStrict_section_mem_range_comp_zero_comp_one_of_sp_eq_spPlace.lean

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

theorem ModularCurve.DRModelPackageLevel.forall_isStrict_section_mem_range_comp_zero_comp_one_of_sp_eq_spPlace

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
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
          ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base) := by sorry
