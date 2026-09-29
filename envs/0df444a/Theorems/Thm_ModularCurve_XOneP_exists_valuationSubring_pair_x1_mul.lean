-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
-- name    : ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/19276954-c59a-5d8b-9649-0ac354849192
-- title:
--   Two valuation subrings of L(X₁(Mp)) above p, with Igusa residue field
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $M\ne 0$ and $p\nmid M$, a field $L$ of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L((q))$ obtained by adjoining to $L$ the coefficientwise image in $L((q))$ of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$ (the field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) inside $\mathbb{Q}((q))$). Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$; let $j\in K$ be nonzero with $q$-expansion the image of $q^{-1}\cdot\mathrm{jNum}$, i.e. of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157); and let $w$ be an integral weight-one form for $\Gamma_1(M)$ over $\kappa=A/\mathfrak{m}_A$, that is, a weight-$1$ modular form on $\Gamma_1(M)$ together with a power series over $\mathbb{Z}$ realising its $q$-expansion and having nonzero image in $\kappa((q))$. Then there exist valuation subrings $W_0,W_1$ of $K$ such that: (i) for each $i\in\{0,1\}$, $W_i$ contains the image of $A$ and every element of $\mathfrak{m}_A$ maps into the nonunits of $W_i$; (ii) for each $i$ and each $P\in A[X]$ whose reduction mod $\mathfrak{m}_A$ is nonzero, both $P(j)$ and $P(j)^{-1}$ lie in $W_i$; (iii) $W_0\ne W_1$; (iv) $W_0$ is the Gauss ring: $f\in W_0$ iff $f\cdot y=x$ in $L((q))$ for some $x,y\in A[[q]]$ with $y\not\equiv 0$ mod $\mathfrak{m}_A$ (series mapped into $L$ and viewed in $L((q))$); (v) any valuation subring of $K$ satisfying the conditions in (i) and (ii) equals $W_0$ or $W_1$; (vi) for every such presentation $f\cdot y=x$ with $\bar y\ne 0$, the ratio $\bar x/\bar y\in\kappa((q))$ lies in the Igusa field $\kappa(X_1(M))(\,\overline{w}^{-1})$, namely the subfield of $\kappa((q))$ generated over the $q$-expansion function field of $\Gamma_1(M)$ over $\kappa$ by the inverse of the reduction of the series of $w$, and $f$ is a nonunit of $W_0$ iff $\bar x=0$; (vii) conversely every element of that Igusa field arises as such a ratio $\bar x/\bar y$ from some $f\in K$.
--
--   This is the valuation-theoretic form of the classical statement that the normalisation of the $j$-line over $A$ in the function field of $X_1(Mp)$ has exactly two branches above the generic point of the $j$-line in characteristic $p$, the branch through the cusp $\infty$ (the Gauss valuation, given by $q$-expansions) having as residue field the Igusa function field $\kappa(\mathrm{Ig}(M;p))$. It is the input to the subsequent analysis of chart rings and integral models of $X_1(Mp)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M) :
    ∃ (W₀ W₁ : ValuationSubring ↥K),

      (∀ i : Fin 2, (∀ a : A, algebraMap A ↥K a ∈ (![W₀, W₁] i)) ∧
        ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ (![W₀, W₁] i).nonunits) ∧

      (∀ i : Fin 2, ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval j P)⁻¹ ∈ (![W₀, W₁] i)) ∧

      W₀ ≠ W₁ ∧

      (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ∧

      (∀ V : ValuationSubring ↥K,
        (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) ∧

      (∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
          ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) ∧
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) ∧
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w →
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z) := by sorry
