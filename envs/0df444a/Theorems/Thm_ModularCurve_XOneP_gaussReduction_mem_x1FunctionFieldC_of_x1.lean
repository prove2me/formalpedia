-- Prove2me | Theorems.Thm_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1
-- name    : ModularCurve.XOneP.gaussReduction_mem_x1FunctionFieldC_of_x1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/158f3686-b254-5b04-9294-dd6ddf4bb19d
-- title:
--   Gauss reductions land in the residual q-expansion field of X₁(M)
-- statement:
--   Fix a prime $p$ and an integer $M$ with $5 \le M$ and $p \nmid M$, and let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, with $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of the elements of [`ModularCurve.x1FunctionFieldC ℚ M`](def/ModularCurve_X1.html#L134), the latter being the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set [`ModularCurve.intFormRatiosC ℚ (Gamma1 M)`](def/ModularCurve_X1.html#L83) of Laurent series attached to $\Gamma_1(M)$. Let $A$ be a discrete valuation domain with fraction field $L$, compatibly an $A$-algebra structure on $K$ over that on $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$. Let $j \in K$ be a nonzero element whose image in $L((q))$ is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= q^{-1}\sum$ (the rational $q$-expansion of $j$). Finally let $f \in K$ and $x, y \in A[[q]]$ be such that the reduction $\bar y$ of $y$ modulo the maximal ideal of $A$ is nonzero and $f \cdot y = x$ holds in $L((q))$, both power series being mapped into $L((q))$ via $A \to L$. The conclusion is that $\bar x/\bar y$, formed in $\kappa((q))$ for $\kappa$ the residue field of $A$, belongs to [`ModularCurve.x1FunctionFieldC κ M`](def/ModularCurve_X1.html#L134), the subfield of $\kappa((q))$ generated over $\kappa$ by [`ModularCurve.intFormRatiosC κ (Gamma1 M)`](def/ModularCurve_X1.html#L83).
--
--   This is one of the two inclusions in the identification of the residue field of the Gauss valuation on the level-$M$ $q$-expansion field $K$ over $L$ with the corresponding $q$-expansion field over the residue field $\kappa$ of $A$; the reverse inclusion is immediate from the definitions. It is used in the construction of the reduction homomorphism on the Gauss valuation ring, in the comparison of $[\,K : L(j)\,]$ with the residual degree over $\kappa(\bar j)$, and in the description of chart rings of $X_1$ in terms of Gauss reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.gaussReduction_mem_x1FunctionFieldC_of_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥K) (x y : PowerSeries A) (hy : y.map (IsLocalRing.residue A) ≠ 0)
    (hxy : (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
      ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M := by sorry
