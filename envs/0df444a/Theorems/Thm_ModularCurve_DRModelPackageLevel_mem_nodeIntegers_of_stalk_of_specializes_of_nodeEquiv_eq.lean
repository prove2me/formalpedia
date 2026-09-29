-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq
-- name    : ModularCurve.DRModelPackageLevel.mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/a35a4095-cca9-53e0-af2f-9d9e002c833c
-- title:
--   Germs at a supersingular crossing lie in the node ring
-- statement:
--   Fix $N_0$ nonzero and a prime $q$ with $q \nmid N_0$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ whose maximal ideal contains $q$ (the predicate `LiesOverPrime`, i.e. $q \in A.\mathrm{nonunits}$), and a ring map $\rho : R_q \to A$ compatible with $R_q \to \overline{\mathbb{Q}}$; let $\mathfrak{P}$ be a `DRModelPackageLevel` datum for $(N_0,q)$, and assume the residue field $\kappa$ of $A$ is algebraically closed of characteristic $q$. Let $O$ be a discrete valuation domain with $\mathfrak{m}_O = (q)$, identified by $eO$ with the contraction of $A$ to the field fixed by the inertia subgroup `A.inertiaSubgroupIn ℚ`, together with $\rho_O : R_q \to O$ whose composite with that embedding into $\overline{\mathbb{Q}}$ is the structure map, and $\mathrm{to}\kappa : O \to \kappa$ given by $\rho_O$-compatible reduction, i.e. $\mathrm{to}\kappa(o)$ is the residue of the element of $A$ corresponding to $eO(o)$. Further data: modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the Hecke maps $\bar\alpha, \bar\beta$ at $(N_0,q)$; a `FibreModel` $fm$ for $N_0$, $A$, $q$, $\kappa$, reduction `residue A`, with a cusp chart $cc$, whose subrings $B_{\mathrm{Fin}}$, $B_{\mathrm{Inf}}$ contain the coefficient-embedded Igusa chart algebras `chartAlgFin N₀ q`, `chartAlgInf N₀ q` (hypotheses `hfin`, `hinf`), surjectivity of the residue map, modular polynomial data `dataAll` for all divisors of $N_0$ with $\Phi_{N_0}$ separable over $\kappa(T)$ after reduction; a place specialisation $P$ with $P.\mathrm{sp} = fm.\mathrm{spPlace}$, and a prolongation tuple $R$ over $P$ with `R.IsModel` (the two divisor laws and the two cusp laws). Assume the special fibre `DRLevel.fibre0` of the level-$N_0$ Igusa scheme over $\kappa$ is integral, and let $n$ be a point of the fibre product of the two component maps $\mathfrak{P}.\mathrm{comp}\,\kappa\,(\mathrm{to}\kappa \circ \rho_O)\,0$ and $\dots 1$; write $x_n$ for the image of $n$ in the $O$-model $\mathfrak{X}_O =$ `pullback (DRLevel.toBase N₀ q) (Spec.map ρO)` under the first projection followed by the $0$th component and by `DRLevel.bcMap ρO toκ`. Assume $\mathfrak{X}_O$ is integral and let $\varphi$ be a ring map from its function field to $\overline{\mathbb{Q}}(X(N_0q))$ (the Laurent base change `modularFunctionFieldBar (N₀ * q)`) which sends germs of global constants from $O$ to their images in $\overline{\mathbb{Q}}$ (`hφO`) and matches the coefficient embedding `coeffEmb` on the chart algebra `chartAlgFin (N₀ * q) q` (`hφj`), the relevant affine chart preimage being nonempty. Assume finally that the images of the generic point of `fibre0` under both components specialise to $x_n$, and that $w$ is a place of `modularFunctionFieldC κ N₀` lying in `ssPlaces q N₀ κ` with $\mathfrak{P}.\mathrm{nodeEquiv}$ labelling $n$ by $w$. Then for every germ $s$ in the stalk of $\mathfrak{X}_O$ at $x_n$, the element $\varphi(s)$ of $\overline{\mathbb{Q}}(X(N_0q))$ lies in `R.nodeIntegers w`: it belongs to the valuation rings $R_1.\mathrm{integers}$ and $R_2.\mathrm{integers}$, and to the valuation ring of every place $V$ of `modularFunctionFieldBar (N₀ * q)` with $P.\mathrm{reduceFst}\,V = w$.
--
--   This is the level-$N_0q$ form of the statement that the local ring of the $O$-model of $X_0(N_0q)$ at a supersingular crossing maps, under the chosen identification $\varphi$ of function fields, into the ring of functions integral at both branches through the node and at all characteristic-zero places reducing to the labelling supersingular place $w$ — the integrality input for the Deligne–Rapoport description of the special fibre. It is used in [`ModularCurve.DRModelPackageLevel.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_chartPresentation`](thm.html#ModularCurve.DRModelPackageLevel.exists_nodeCoordinates_and_forall_mem_support_iff_chainPos_of_chartPresentation), where node coordinates at the crossing are produced from germs in this stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq.lean

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
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI

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
open Classical in

theorem ModularCurve.DRModelPackageLevel.mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (ρ : DRLevel.R q →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (𝔓 : DRModelPackageLevel N₀ q hqN)

    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
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
    (hR : R.IsModel)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]

    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)))
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n)) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n) trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hsp₀ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n))
    (hsp₁ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n))

    (w : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) (hw : w ∈ ssPlaces q N₀ (ResidueField ↥A))
    (hn : ((𝔓.nodeEquiv (ResidueField ↥A) (toκ.comp ρO) n : ↥(ssPlaces q N₀ (ResidueField ↥A))) : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) = w) :
    ∀ s : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n), φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) s) ∈ R.nodeIntegers w := by sorry
