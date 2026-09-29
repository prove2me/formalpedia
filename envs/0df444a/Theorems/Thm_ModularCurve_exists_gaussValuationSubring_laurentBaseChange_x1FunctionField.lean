-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
-- name    : ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/54ff7aa9-7455-5090-8230-85a7ae14911e
-- title:
--   Gauss valuation subring of the q-expansion field of X₁(N)
-- statement:
--   Let $N \geq 1$ and let $L$ be a field of characteristic $0$. Let $K$ be an intermediate field of the Laurent series field $L((q))$ over $L$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield of $L((q))$ generated over $L$ by the image of the $q$-expansion function field $\mathbb{Q}(X_1(N)) \subseteq \mathbb{Q}((q))$ under the coefficientwise extension of $\mathbb{Q} \to L$. Let $A$ be a discrete valuation ring which is an $L$-algebra with $L$ as its fraction field, together with an $A$-algebra structure on $K$ compatible with that of $L$, and let $j \in K$ be an element whose image in $L((q))$ is the coefficientwise image of $q^{-1}$ times the integral power series $jNumQ$, i.e. the $q$-expansion of the modular invariant $j$; $j$ is assumed nonzero. Then there is a valuation subring $W_0$ of $K$ such that: $f \in W_0$ exactly when $f \cdot y = x$ in $L((q))$ for some $x, y \in A[[q]]$ whose coefficients are pushed to $L$ and with $y$ having nonzero reduction modulo the maximal ideal of $A$; every element of $A$ lies in $W_0$; every element of the maximal ideal of $A$ maps to a nonunit of $W_0$; for every $P \in A[X]$ with nonzero reduction, both $P(j)$ and $P(j)^{-1}$ lie in $W_0$; and, for every $f$ and every such presentation $f \cdot y = x$, $f$ is a nonunit of $W_0$ precisely when $x$ reduces to $0$ modulo the maximal ideal.
--
--   This is the Gauss (content) valuation on $A[[q]]$ transported to the $q$-expansion function field of $X_1(N)$ over $\operatorname{Frac} A$, presented by the explicit ratio criterion together with the facts that $A$ is contained in the valuation ring, that the maximal ideal of $A$ consists of nonunits, and that polynomial expressions in $j$ with nonzero reduction are units. It underpins the computation of residue field degrees and of the Gauss reduction for $X_1$ at levels $M$ and $Mp$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ W₀ : ValuationSubring ↥K,
      (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ∧
      (∀ a : A, algebraMap A ↥K a ∈ W₀) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀) ∧
      (∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) := by sorry
