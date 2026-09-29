-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/e2e6d7f4-d94c-5b00-870b-0f334ca08064
-- title:
--   Pic⁰-point of D classifying 𝒪(ξ₁-ξ₂)
-- statement:
--   Fix a prime $p$, an integer $M \ge 5$ with $p \nmid M$, a characteristic-zero field $L$ that is a $p$-cyclotomic extension of $\mathbb Q$ with a primitive $p$-th root of unity $\zeta$, and let $K \subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image of the function field of $X_1(Mp)$. Let $A$ be a discrete valuation ring with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in its image, acting on $K$ compatibly, and let $j \in K$, $j \ne 0$, have Laurent expansion the $q$-expansion of the modular function $j$. Write $X = \mathrm{ModularCurve.TwoChartModel}\,A\,K\,j$ for the two-chart model, with structure morphism $f = \mathrm{modelTo}$ to $\mathrm{Spec}\,A$, assumed proper and flat, with smooth geometrically integral base change to $L$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1 : C_1 \to \mathrm{Spec}\,k$, $c_2 : C_2 \to \mathrm{Spec}\,k$ be proper, smooth of relative dimension $1$ and geometrically integral, with closed immersions $i_1, i_2$ of $C_1$, $C_2$ into the base change $X_k$ over $\mathrm{Spec}\,k$ whose images cover $X_k$, such that the scheme-theoretic intersection $\mathrm{pullback}\,i_1\,i_2$ is reduced with $n > 0$ points. Let $\varepsilon$ be a section of $f$, let $\varepsilon_1, \varepsilon_2$ be sections of $c_1, c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$, and let $D$ be a relative $\mathrm{Pic}^0$ designation for $f$ (a scheme over $\mathrm{Spec}\,A$ with zero section) which is assumed to represent, via some datum $\mathrm{hrep}$ with Poincaré bundle $\mathcal P$, the functor of rigidified line bundles on $X$ satisfying the fibrewise algebraic-equivalence-to-zero condition $\mathrm{algEquivZeroCut}$. Let $U$ be the largest open of $X$ on which $f$ is smooth of relative dimension $1$. Finally let $Pl$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit, together with a lift $\rho : A \to Pl$ of $A \to \overline{\mathbb Q}$ and a surjection $\pi_k : Pl \to k$ with $\pi_k \circ \rho$ the structure map $A \to k$. The assertion: for all $Pl$-points $\xi_1, \xi_2$ of $X$ over $\mathrm{Spec}\,\rho$ with images contained in $U$, and all $k$-points $d_1, d_2$ of $C_2$ such that, for $m = 1, 2$, the composite of $d_m$, $i_m$-inclusion $i_2$ and the first projection $X_k \to X$ equals $\mathrm{Spec}\,\pi_k$ followed by $\xi_m$, and the image of the closed point of $\mathrm{Spec}\,k$ under $d_m$ followed by $i_2$ does not lie in the image of $i_1$, there exists a $Pl$-point $s$ of $D$ over $\mathrm{Spec}\,\rho$ such that the pullback of $\mathcal P$ along $s$ has underlying module isomorphic to the tensor product of the inverse ideal module of the relative effective Cartier divisor $\mathrm{ofPoint}$ attached to $\xi_1$ with the ideal module of the one attached to $\xi_2$, i.e. to $\mathcal O(\xi_1) \otimes \mathcal O(-\xi_2)$.
--
--   This is the Abel–Jacobi step for the two-chart model of $X_1(Mp)$ over a discrete valuation ring: the difference of two $Pl$-points lying in the smooth locus, whose reductions are points of the second glued component $C_2$ away from $C_1$, defines a $Pl$-valued point of the representing object for the relative $\mathrm{Pic}^0$ functor. It is the variant in which both reductions meet $C_2$ rather than $C_1$, and feeds the computations identifying reductions of divisor classes in the degenerate fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    [Flat (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      d₂.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) := by sorry
