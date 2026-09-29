-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_gaussReduction_mem_x1x0FunctionFieldC_of_x1x0
-- name    : ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1x0FunctionFieldC_of_x1x0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/01606dc4-27bc-5cac-a7a1-21b478ea5526
-- title:
--   Gauss reduction preserves the level Γ₁(M)∩Γ₀(p) q-expansion field
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$, let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ for the set $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K_1$ be an intermediate field of $L \subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of the elements of the subfield of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set [`ModularCurve.intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 p)`](def/ModularCurve_X1.html#L83) of integral-expansion ratios for the group $\Gamma_1(M) \cap \Gamma_0(p)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, with $K_1$ an $A$-algebra compatibly with $A \to L \to K_1$. Let $f \in K_1$ and $x, y \in A[[q]]$ be such that the reduction of $y$ modulo the maximal ideal is nonzero and $f \cdot y = x$ in $L((q))$, the power series being mapped coefficientwise by $A \to L$ and embedded as Laurent series. Then the quotient $\bar x / \bar y$ of the reductions, viewed in $k((q))$ for $k$ the residue field of $A$, lies in [`ModularCurve.x1x0FunctionFieldC k M p`](def/ModularCurve_X1.html#L142), the subfield of $k((q))$ generated over $k$ by [`ModularCurve.intFormRatiosC k (Gamma1 M ⊓ Gamma0 p)`](def/ModularCurve_X1.html#L83).
--
--   This is the level-preserving half of the reduction of the $q$-expansion function field of $X_1(M) \cap X_0(p)$ modulo a prime above $p$: Gauss reduction of an element that is $p$-integral in the sense of admitting a power-series numerator and denominator lands in the function field of the same level in characteristic $p$. It feeds the companion statement [`ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1FunctionFieldC_of_x1x0`](thm.html#ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1FunctionFieldC_of_x1x0), where the $\Gamma_0(p)$-structure is removed and only the level $\Gamma_1(M)$ remains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_gaussReduction_mem_x1x0FunctionFieldC_of_x1x0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1x0FunctionFieldC_of_x1x0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
        (f : ↥K₁) (x y : PowerSeries A) (hy : y.map (IsLocalRing.residue A) ≠ 0)
    (hxy : (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
      ∈ ModularCurve.x1x0FunctionFieldC (IsLocalRing.ResidueField A) M p := by sorry
