-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_gauss_heckeRoof_x1_mul
-- name    : ModularCurve.XOneP.exists_valuationSubring_gauss_heckeRoof_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/641f8a74-08ce-59fd-b8a5-cedc4b2b7de1
-- title:
--   A Gauss valuation subring of the Hecke roof function field
-- statement:
--   Fix a prime $p$, an integer $M\ne 0$ with $5\le M$ and $p\nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, an element $\zeta\in L$ that is a primitive $p$-th root of unity, and a commutative domain $A$ which is a discrete valuation ring, equipped with an $A$-algebra structure on $L$ realising $L$ as the fraction field of $A$, such that $p$ lies in the maximal ideal $\mathfrak m_A$ and $\zeta$ lies in the image of $A$; fix also a prime $\ell$. Write $K$ for the intermediate field `laurentBaseChange L (x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))` of $L((q))$ over $L$, that is, the subfield generated over $L$ by the coefficientwise image under $\mathbb{Q}\to L$ of the subfield of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set `intFormRatiosC ℚ (Gamma1 (M * p) ⊓ Gamma0 (M * p * ℓ))` of ratios attached to the group $\Gamma_1(Mp)\cap\Gamma_0(Mp\ell)$. Assume $K$ carries an $A$-algebra structure compatible with $A\to L\to K$, and let $j_\ell\in K$ be a nonzero element whose underlying Laurent series is the coefficientwise image in $L((q))$ of $q^{-1}$ times the power series `jNumQ`, i.e. of the $q$-expansion `jq`. Then there is a valuation subring $W\subseteq K$ with the following five properties: the image of $A$ in $K$ lies in $W$; the image of every element of $\mathfrak m_A$ lies in the non-units of $W$; for every $P\in A[X]$ whose reduction modulo $\mathfrak m_A$ is nonzero, both $P(j_\ell)$ and $P(j_\ell)^{-1}$ lie in $W$; an element $f\in K$ lies in $W$ if and only if there are $x,y\in A[[q]]$ with $y$ having nonzero reduction modulo $\mathfrak m_A$ and $f\cdot\hat y=\hat x$ in $L((q))$, where $\hat{\;\cdot\;}$ denotes the image of a power series over $A$ in $L((q))$; and, for every $f\in K$ and all $x,y\in A[[q]]$ with $y$ of nonzero reduction and $f\cdot\hat y=\hat x$, the element $f$ is a non-unit of $W$ exactly when the reduction of $x$ modulo $\mathfrak m_A$ vanishes.
--
--   This constructs the Gauss valuation of $L((q))$, restricted to the function field of the Hecke correspondence roof $X_1(Mp)\cap X_0(Mp\ell)$ over $L$, together with an explicit presentation of its members and its non-units in terms of $q$-expansions with coefficients in $A$, and with invertibility of the values $P(j_\ell)$ for $P$ of nonzero reduction. It feeds the comparison of valuation subrings at the Gauss centre used in the level-changing part of the argument, via [`ModularCurve.XOneP.forall_valuationSubring_heckeRoof_gaussCentre_alpha_iff_beta_x1_mul`](thm.html#ModularCurve.XOneP.forall_valuationSubring_heckeRoof_gaussCentre_alpha_iff_beta_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_valuationSubring_gauss_heckeRoof_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_valuationSubring_gauss_heckeRoof_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))] [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)] :
    ∃ W : ValuationSubring ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))),
      (∀ a : A, algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) a ∈ W) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))) a ∈ W.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval jℓ P ∈ W ∧ (Polynomial.aeval jℓ P)⁻¹ ∈ W) ∧
      (∀ f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), f ∈ W ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ∧
      (∀ (f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) := by sorry
