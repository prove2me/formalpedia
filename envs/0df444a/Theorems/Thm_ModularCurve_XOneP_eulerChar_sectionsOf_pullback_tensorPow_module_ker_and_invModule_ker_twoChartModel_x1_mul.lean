-- Prove2me | Theorems.Thm_ModularCurve_XOneP_eulerChar_sectionsOf_pullback_tensorPow_module_ker_and_invModule_ker_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.eulerChar_sectionsOf_pullback_tensorPow_module_ker_and_invModule_ker_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/67ed3f05-fde3-586f-94c0-19cf1b782858
-- title:
--   Euler characteristics of twists by the component C₂
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a $p$-cyclotomic extension of $\mathbb{Q}$, a primitive $p$-th root of unity $\zeta\in L$, and an intermediate field $K$ of $L\subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise images of the $q$-expansion function field of $X_1(Mp)$; let $A$ be a discrete valuation domain with fraction field $L$ whose maximal ideal contains $p$ and which contains $\zeta$, with $K$ an $A$-algebra over $A\subseteq L$, and let $j\in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Write $X=$ [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229), proper over $\operatorname{Spec}A$ via [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), and assume a section $\varepsilon$ and a relative $\mathrm{Pic}^0$ designation $D$ (a scheme over $\operatorname{Spec}A$ with zero section) representing the subfunctor of rigidified line bundles that are fibrewise algebraically equivalent to zero. Let $k$ be an algebraically closed $A$-algebra of characteristic $p$, and let $C_1,C_2$ be proper, smooth of relative dimension $1$, geometrically integral and integral over $k$, closed-immersed over $k$ by $i_1,i_2$ into the base change $X\times_A k$; assume the images of $i_1,i_2$ cover all points of $X\times_A k$, that the scheme-theoretic intersection $C_1\times_{X\times_Ak}C_2$ is reduced with exactly $n>0$ points, and that there are $n$ $k$-points $z_i$ of this intersection, each mapping to sections of $C_1\to\operatorname{Spec}k$ and $C_2\to\operatorname{Spec}k$, with pairwise distinct closed points. Let $O$ be a discrete valuation domain with a ring map $\rho_O:A\to O$ carrying the maximal ideal of $A$ onto that of $O$, together with $\mathrm{to}\kappa:O\to k$ satisfying $\mathrm{to}\kappa\circ\rho_O=\,$the structure map $A\to k$, and let $bc:X\times_Ak\to X\times_AO$ be compatible with the first projections and with the second projections via $\operatorname{Spec}(\mathrm{to}\kappa)$. Let $\mathcal V_1,\mathcal V_2$ be two-chart affine open covers of $C_1,C_2$ and $d\in\mathbb{N}$. Write $I$ for the kernel ideal sheaf of $i_2$ followed by $bc$ on $X\times_AO$, $I.\mathrm{module}$ for the associated module (the kernel of the unit map to the pushforward of the unit along the closed subscheme inclusion), $I.\mathrm{invModule}$ for its dual, and, for a module $\mathcal F$ on $C_\nu$, $\chi_\nu(\mathcal F)=\dim_k H^0-\dim_k H^1$ of the two-chart Čech complex `𝒱ᵥ.sectionsOf cᵥ 𝓕` (kernel and cokernel of the difference of the two restriction maps). Then, with $\mathcal O_{C_\nu}$ the unit module, $$\chi_1\big((i_1\!\cdot\! bc)^*(I.\mathrm{module}^{\otimes d})\big)=\chi_1(\mathcal O_{C_1})-dn,\quad \chi_2\big((i_2\!\cdot\! bc)^*(I.\mathrm{module}^{\otimes d})\big)=\chi_2(\mathcal O_{C_2})+dn,$$ $$\chi_1\big((i_1\!\cdot\! bc)^*(I.\mathrm{invModule}^{\otimes d})\big)=\chi_1(\mathcal O_{C_1})+dn,\quad \chi_2\big((i_2\!\cdot\! bc)^*(I.\mathrm{invModule}^{\otimes d})\big)=\chi_2(\mathcal O_{C_2})-dn,$$ where $i_\nu\!\cdot\! bc$ denotes $i_\nu$ followed by $bc$ and tensor powers are formed by $\mathrm{tensorPow}$.
--
--   This is the numerical input of the intersection theory of a special fibre with two components meeting in $n$ points: twisting by the ideal sheaf of one component lowers the Euler characteristic on that component by the intersection number and raises it on the other, with the dual twist reversing the signs. It is used in the line-bundle extension argument for the component group of the Jacobian of $X_1(Mp)$, where it feeds the existence statement for tensor-power twists with prescribed Euler characteristics.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_eulerChar_sectionsOf_pullback_tensorPow_module_ker_and_invModule_ker_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.eulerChar_sectionsOf_pullback_tensorPow_module_ker_and_invModule_ker_twoChartModel_x1_mul
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
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (z : Fin n → (Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1))
    (hz₁ : ∀ i, (z i ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : ∀ i, (z i ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _)
    (hzinj : Function.Injective fun i => (z i).base (IsLocalRing.closedPoint k))
    [IsIntegral C₁] [IsIntegral C₂]
    (𝒱₁ : C₁.TwoAffineOpenCover) (𝒱₂ : C₂.TwoAffineOpenCover) (d : ℕ) :
    (Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback (i₁.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).module).tensorPow d))).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback (i₁.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).module).tensorPow d))).H1 =
        (Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H1 - d * n ∧
    (Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback (i₂.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).module).tensorPow d))).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback (i₂.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).module).tensorPow d))).H1 =
        (Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H1 + d * n ∧
    (Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback (i₁.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).invModule).tensorPow d))).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ ((Scheme.Modules.pullback (i₁.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).invModule).tensorPow d))).H1 =
        (Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₁.sectionsOf c₁ (SheafOfModules.unit C₁.ringCatSheaf : C₁.Modules)).H1 + d * n ∧
    (Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback (i₂.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).invModule).tensorPow d))).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ ((Scheme.Modules.pullback (i₂.1 ≫ bc)).obj ((((i₂.1 ≫ bc).ker).invModule).tensorPow d))).H1 =
        (Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H0 : ℤ) -
          Module.finrank k (𝒱₂.sectionsOf c₂ (SheafOfModules.unit C₂.ringCatSheaf : C₂.Modules)).H1 - d * n := by sorry
