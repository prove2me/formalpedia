-- Prove2me | Theorems.Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.proj_snd_eq_zero_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/b9e82c08-37dd-5ff2-b09a-877174fd3374
-- title:
--   Vanishing of the J^E-component off the second component
-- statement:
--   Fix a prime $p$, an integer $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a $p$-cyclotomic extension of $\mathbb{Q}$ and a primitive $p$-th root of unity $\zeta \in L$; let $K$ be the subfield of $\mathrm{LaurentSeries}\,L$ generated over $L$ by the image of the function field of $X_1(Mp)$ under the coefficientwise embedding, let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j \in K$ be the element whose Laurent expansion is $\mathrm{jq}$, assumed nonzero. Let $X =$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) with its structure morphism $f$ to $\operatorname{Spec} A$, assumed proper, and let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. The data consist of: two proper smooth geometrically integral curves $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ of relative dimension $1$ with closed immersions $i_1, i_2$ into the base change $X_k$ over $k$ whose images cover $X_k$, with $\mathrm{pullback}\, i_1\, i_2$ reduced of cardinality $n > 0$; a section $\varepsilon$ of $f$ and sections $\varepsilon_1, \varepsilon_2$ of $c_1, c_2$ with $\varepsilon_1$ followed by $i_1$ the base change of $\varepsilon$; a relative $\mathrm{Pic}^0$ designation $D$ for $f$ (a scheme over $\operatorname{Spec} A$ with a zero section) representing, via a Poincaré rigidified line bundle, the subfunctor of rigidified line bundles that are fibrewise algebraically equivalent to zero, with $D.\mathrm{toBase}$ smooth and separated, together with the corresponding representability `hreps` for $X_k$ by $D$ base changed to $k$ and an isomorphism `hPk` identifying its Poincaré bundle with the one obtained from $D$ by base change, and designations $D_1, D_2$ representing the analogous functors for $c_1, c_2$; a morphism $\nu_2$ over $k$ from $(D \times_A k).\mathrm{toBase}$ to $D_2.\mathrm{toBase}$ characterised by the property that for every $k$-scheme point $a$ of $(D \times_A k).\mathrm{toBase}$ the Poincaré bundle of $D_2$ pulled back along $a$ followed by $\nu_2$ is the rigidification along $\varepsilon_2$ of the pullback along `curveChange` $i_2$ of the bundle classified by $a$. Further, $G$ is a [`ModularCurve.JOneP.NeronSpecialFibreGeom p`](def/ModularCurve_JOnePGeom.html#L9), i.e. abelian groups $J^0_s$ (with a subgroup `torus`), $J^I$, $J^E$ and a surjection $\mathrm{proj} : J^0_s \to J^I \times J^E$ with kernel `torus`; bijections `pts`, `ptsI`, `ptsE` of these groups with the $k$-points of $(D\times_A k).\mathrm{toBase}$, $D_1.\mathrm{toBase}$, $D_2.\mathrm{toBase}$ turning addition into tensor product of the pulled-back Poincaré bundles, and compatible with $\mathrm{proj}$ in the sense that the first component of $\mathrm{proj}\,x$ corresponds to `pts x` followed by the morphism of designations induced by $i_1$ and the second to `pts x` followed by $\nu_2$. Finally $U$ is the largest open of $X$ on which $f$ is smooth of relative dimension $1$, $Pl$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit in it, $\rho : A \to Pl$ lifts the structure map $A \to \overline{\mathbb{Q}}$, and $\pi_k : Pl \to k$ is a surjection with $\pi_k \circ \rho$ the structure map $A \to k$. The conclusion: for all $Pl$-points $\xi_1, \xi_2$ of $X$ over $\operatorname{Spec}\rho$ whose images lie in $U$, and all $k$-points $d_1, d_2$ of $C_1$ such that $d_i$ followed by $i_1$ and the projection to $X$ equals $\operatorname{Spec}\pi_k$ followed by $\xi_i$ and such that the image of the closed point of $\operatorname{Spec} k$ under $d_i$ followed by $i_1$ avoids the image of $i_2$, and for every $Pl$-point $s$ of $D.\mathrm{toBase}$ for which the Poincaré bundle of $D$ pulled back along $s$ is isomorphic to the dual of the ideal of the graph of $\xi_1$ tensored with the ideal of the graph of $\xi_2$, every $y \in J^0_s$ whose point `pts y` is the reduction of $s$ along $\pi_k$ satisfies $(\mathrm{proj}\,y)_2 = 0$.
--
--   This is the per-pair vanishing step in the analysis of the special fibre of the Néron model of the Jacobian of $X_1(Mp)$ at $p$: a degree-zero class on the two-chart model represented by $\mathcal{O}(\xi_1) \otimes \mathcal{O}(\xi_2)^{-1}$ with both points reducing into the first component and away from the second has trivial restriction to the second component, hence zero $J^E$-coordinate. It feeds the statement that the classes supported in this way lie in the toric part, obtained by summing over the support of a divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_proj_snd_eq_zero_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.proj_snd_eq_zero_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul
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
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      d₂.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₁.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₂.1.base →
      ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) →
        ∀ (y : G.J0s),
          (pts y).1 ≫ pullback.fst D.toBase (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ s.1 →
          (G.proj y).2 = 0 := by sorry
