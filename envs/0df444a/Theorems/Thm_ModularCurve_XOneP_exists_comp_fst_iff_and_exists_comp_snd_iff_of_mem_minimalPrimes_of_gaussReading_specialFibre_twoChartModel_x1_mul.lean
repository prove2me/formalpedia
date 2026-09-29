-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_comp_fst_iff_and_exists_comp_snd_iff_of_mem_minimalPrimes_of_gaussReading_specialFibre_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_comp_fst_iff_and_exists_comp_snd_iff_of_mem_minimalPrimes_of_gaussReading_specialFibre_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/0b232b95-fe99-5f55-a487-52c6a8f01a97
-- title:
--   Oriented branch dictionary for the special fibre of X₁(Mp)
-- statement:
--   Let $p$ be a prime, $M\ge 5$ an integer with $p\nmid M$, $L$ a characteristic-zero field that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and $\zeta\in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of the $q$-expansion function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$, let $A$ be a discrete valuation ring with fraction field $L$ whose maximal ideal contains $p$ and which contains a preimage of $\zeta$, with uniformiser $\varpi$, and with $K$ an $A$-algebra compatibly with $L$; let $j\in K$ be nonzero with Laurent expansion the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Write $R=$ [`ModularCurve.TwoChart.chartAlgFin A ↥K j`](def/ModularCurve_TwoChartModel.html#L135) for the algebra of elements of $K$ integral over $A[j]$, $X$ for the two-chart model [`ModularCurve.TwoChartModel`](def/ModularCurve_TwoChartModel.html#L229), assumed proper over $\operatorname{Spec} A$, and `ιFin` for its finite chart $\operatorname{Spec} R\to X$. Let $k$ be an algebraically closed $A$-algebra of characteristic $p$, and let $c_1:C_1\to\operatorname{Spec} k$, $c_2:C_2\to\operatorname{Spec} k$ be proper, smooth of relative dimension one, geometrically integral, equipped with closed immersions $i_1,i_2$ into the special fibre $X\times_A k$ over $k$ whose images cover every point of it, such that the fibre product of $i_1$ and $i_2$ is reduced and has exactly $n>0$ points. On the $C_1$ side, fix an integral weight-one form $w$ for $\Gamma_1(M)$ over $k$ (a weight-one modular form on $\Gamma_1(M)$ together with an integral power series that is its $q$-expansion, whose image in $k((q))$ is nonzero), a curve model $\mathrm{Mdl}_1$ over $k$ for the Igusa function field obtained by adjoining the inverse of that image to the $\Gamma_1(M)$ $q$-expansion field over $k$, and an isomorphism $e_1:\mathrm{Mdl}_1.C\cong C_1$ compatible with the structure maps; assume the preimage of the finite chart under $e_1$ followed by $i_1$ followed by the first projection is nonempty, and assume the Gauss reading hypothesis: for all $a\in R$ and power series $x,y$ over $A$ with $y$ having nonzero reduction and $a\cdot y=x$ in $L((q))$, the section $a$ pulls back along that composite to the element of the Igusa function field (via $\mathrm{Mdl}_1$'s function-field identification) whose Laurent series is $\bar x/\bar y$. Finally let $W_0$ be the valuation subring of $K$ consisting of those $f$ admitting such an expression $f\cdot y=x$ with $\bar y\ne 0$, and let $\mathfrak{P}_0\ne\mathfrak{P}_1$ be minimal primes over $\varpi R$ with $\mathfrak{P}_0$ equal to the set of $b\in R$ whose image in $K$ is a non-unit of $W_0$. Then for every ring homomorphism $\chi:R\to k$ extending $A\to k$: there is a $k$-point $c$ of $C_1$ with $c$ followed by $i_1$ followed by the first projection equal to $\operatorname{Spec}(\chi)$ followed by `ιFin`, whose image avoids the image of the first projection of the fibre product of $i_1$ and $i_2$, if and only if $\mathfrak{P}_0\subseteq\ker\chi$ and $\mathfrak{P}_1\not\subseteq\ker\chi$; and symmetrically there is such a $k$-point of $C_2$ avoiding the image of the second projection if and only if $\mathfrak{P}_1\subseteq\ker\chi$ and $\mathfrak{P}_0\not\subseteq\ker\chi$.
--
--   This is the oriented dictionary between the two irreducible components of the geometric special fibre of the two-chart model of $X_1(Mp)$ at $p$ — the two Igusa components meeting at the supersingular points — and the two minimal primes of the uniformiser in the finite chart algebra, the component carrying the Gauss ($q$-expansion) reading being the one matched with $\mathfrak{P}_0$. It is used in the subsequent identification of finite-chart $k$-points with points of each component away from the crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_comp_fst_iff_and_exists_comp_snd_iff_of_mem_minimalPrimes_of_gaussReading_specialFibre_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
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

theorem ModularCurve.XOneP.exists_comp_fst_iff_and_exists_comp_snd_iff_of_mem_minimalPrimes_of_gaussReading_specialFibre_twoChartModel_x1_mul
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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (𝔓₀ 𝔓₁ : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (h𝔓₀min : 𝔓₀ ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes)
    (h𝔓₁min : 𝔓₁ ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes)
    (h𝔓₀₁ : 𝔓₀ ≠ 𝔓₁)
    (h𝔓₀ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), b ∈ 𝔓₀ ↔ (b : ↥K) ∈ W₀.nonunits) :
    ∀ (χ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* k), χ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = algebraMap A k →
      ((∃ c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
          c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom χ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j ∧
          ∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ↔
        (𝔓₀ ≤ RingHom.ker χ ∧ ¬ 𝔓₁ ≤ RingHom.ker χ)) ∧
      ((∃ c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂,
          c.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom χ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j ∧
          ∀ t, c.1.base t ∉ Set.range (pullback.snd i₁.1 i₂.1).base) ↔
        (𝔓₁ ≤ RingHom.ker χ ∧ ¬ 𝔓₀ ≤ RingHom.ker χ)) := by sorry
