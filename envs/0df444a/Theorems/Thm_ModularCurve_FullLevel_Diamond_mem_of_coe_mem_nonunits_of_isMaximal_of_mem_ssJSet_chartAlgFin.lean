-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin
-- name    : ModularCurve.FullLevel.Diamond.mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/e9be5f54-bbb0-51d2-afb4-c50bce5ee86a
-- title:
--   Gauss nonunits lie in the supersingular maximal ideal
-- statement:
--   Fix a prime $q$ and $M'\neq 0$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11 \pmod{12}$ and $\ell_g\mid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, let $k_0/\mathbb Q$ be a subfield of $\overline{\mathbb Q}$ and $\pi_0\in k_0$ an element lying in $A$, and put $A_0=A\cap k_0$ (the comap of $A$ along $k_0\to\overline{\mathbb Q}$); assume $A_0$ is a discrete valuation ring with maximal ideal $(\pi_0)$, henselian, with algebraically closed residue field, and that every element of $A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0$ lying in $A$. Assume further $\xi\in k_0$ is a primitive $(q\ell_g)$-th root of unity and some ring homomorphism $k_0\to\mathbb C$ carries $\xi$ to $e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of `levelH q M'`, the kernel of reduction to $(\mathbb Z/q)^\times$, with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K\subseteq k_0((t))$ be the field generated over $k_0$ by the coefficientwise image of the $q$-expansion function field `xHFunctionField (q ^ 2 * M') H₁`, with $A_0$-algebra and scalar-tower structure on $K$. Let $j\in K$ be the element whose Laurent series is the image of the $j$-expansion `jq`, assumed nonzero, and let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are power series $x,y$ over $A_0$ with $y$ nonzero modulo the maximal ideal and $f\cdot y=x$ in $k_0((t))$. Let $C'$ be the $A_0$-subalgebra of $K$ of elements integral over $A_0[j]$, and $y'$ a maximal ideal of $C'$ containing the image of $\pi_0$, such that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi:C'\to\Omega$ with kernel $y'$, the value $\varphi(j)$ lies in `ssJSet q Ω`, i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. Then every $h\in C'$ whose image in $K$ is a nonunit of $W_0$ belongs to $y'$.
--
--   This places the centre of the Gauss chart — the point of the integral model of $X_{H_1}(q^2M')$ over $A_0$ cut out by the maximal ideal of the Gauss valuation ring — inside the given supersingular closed point, so that the two local rings may be compared. It feeds the construction of supersingular points with prescribed level structure on the Drinfeld full-level models used in the Diamond and auxiliary level-one arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical
attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.Diamond.mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), y.map (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ≠ 0 ∧
      (f : LaurentSeries ↥k₀) * HahnSeries.ofPowerSeries ℤ ↥k₀ (y.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀))
        = HahnSeries.ofPowerSeries ℤ ↥k₀ (x.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)))
    (y' : {y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) // y.IsMaximal ∧ algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y})
    (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* Ω), RingHom.ker φ = y'.1 →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))

    (hh : ((h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) ∈ W₀.nonunits) :
    h ∈ y'.1 := by sorry
