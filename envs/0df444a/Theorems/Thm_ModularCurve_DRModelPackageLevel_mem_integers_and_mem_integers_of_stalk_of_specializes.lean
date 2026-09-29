-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_integers_and_mem_integers_of_stalk_of_specializes
-- name    : ModularCurve.DRModelPackageLevel.mem_integers_and_mem_integers_of_stalk_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/ac538297-59cb-5e57-9c1f-6fc37d0ac58e
-- title:
--   Germs at a point met by both branches lie in both prolongations
-- statement:
--   Fix a nonzero $N_0$ and a prime $q$ with $q \nmid N_0$, a valuation subring $A$ of $\overline{\mathbf Q}$ whose residue field is algebraically closed of characteristic $q$, and a level-$N_0q$ Deligne–Rapoport model package $\mathfrak P$ for the Igusa-type model `DRLevel.toBase N₀ q` over $\mathrm{Spec}\,(\mathrm{DRLevel.R}\, q)$. Let $O$ be a discrete valuation domain, $e_O$ a ring isomorphism of $O$ onto the valuation subring obtained by pulling $A$ back along the inclusion of the fixed field of `A.inertiaSubgroupIn ℚ`, with $\mathfrak m_O = (q)$, let $\rho_O : \mathrm{DRLevel.R}\, q \to O$ satisfy that composing it with $e_O$ and the inclusions into $\overline{\mathbf Q}$ recovers the structure map, and let $\mathrm{to}\kappa : O \to \mathrm{ResidueField}\,A$ be the map sending $o$ to the residue of the corresponding element of $A$. Given modular polynomial data `data` for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy embeddings $\bar\alpha, \bar\beta$ at level $N_0$, a place specialisation $P$ at $A$ with values in $\mathrm{ResidueField}\,A$, and a prolongation tuple $R$ for $P$ (in particular two regular prolongations $R_1$, $R_2$ of $A$ to $\overline{\mathbf Q}(X(N_0q))$ in the form `modularFunctionFieldBar (N₀ * q)`), assume that `DRLevel.fibre0` over $\mathrm{to}\kappa \circ \rho_O$ is integral. Let $x$ be a point of the integral base change $\mathfrak X_O =$ `pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))`, and $\varphi$ a ring homomorphism from its function field into `modularFunctionFieldBar (N₀ * q)` which is pinned in two ways: on constants, $\varphi$ carries the germ at $x$ of the global section coming from $a \in O$ to the constant given by the image of $a$ in $\overline{\mathbf Q}$; and on the finite Igusa chart (whose preimage is assumed nonempty), $\varphi$ carries the germ of each element $a$ of `IgusaScheme.chartAlgFin (N₀ * q) q` to the coefficientwise image in $\overline{\mathbf Q}$ of the Laurent expansion of $a$. Assume finally that for $i = 0$ and $i = 1$ the image of the generic point of `DRLevel.fibre0` under the base map of $\mathfrak P.\mathrm{comp}$ at index $i$ followed by the base-change morphism `DRLevel.bcMap ρO toκ` specialises to $x$. Then for every germ $s$ in the stalk of $\mathfrak X_O$ at $x$, the image $\varphi(s)$ in `modularFunctionFieldBar (N₀ * q)` lies both in `R.R₁.integers` and in `R.R₂.integers`.
--
--   This is the level-$\Gamma_0(N_0q)$ form of the statement that a point of the $O$-model to which the generic points of both components of the mod-$q$ fibre specialise has its local ring carried by the pinned reading $\varphi$ into both Gauss prolongations of $A$ to the modular function field, the two prolongations corresponding to the two branches of the Deligne–Rapoport fibre. It feeds the analysis of germs at the nodes, being cited by [`ModularCurve.DRModelPackageLevel.mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq`](thm.html#ModularCurve.DRModelPackageLevel.mem_nodeIntegers_of_stalk_of_specializes_of_nodeEquiv_eq), in the reduction-theoretic input to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mem_integers_and_mem_integers_of_stalk_of_specializes.lean

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

theorem ModularCurve.DRModelPackageLevel.mem_integers_and_mem_integers_of_stalk_of_specializes

    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)}

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
    (P : PlaceSpecialization A q N₀ data hKr (ResidueField ↥A) (residue ↥A) hα hβ)
    (R : ProlongationTuple P)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]

    (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))
    [hint : IsIntegral (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))]
    (φ : ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) →+* ↥(modularFunctionFieldBar (N₀ * q)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x) _
        (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)) (((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))) a))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      ((φ ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).germToFunctionField ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) ⁻¹ᵁ ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤))
          (((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).app ((IgusaScheme.ιFin (N₀ * q) q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin (N₀ * q) q).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).inv a)))) : ↥(modularFunctionFieldBar (N₀ * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hsp₀ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)
    (hsp₁ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x) :
    ∀ s : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x,
      φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) s) ∈ R.R₁.integers ∧
      φ (algebraMap _ ↥((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).functionField) s) ∈ R.R₂.integers := by sorry
