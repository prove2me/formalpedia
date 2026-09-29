-- Prove2me | Theorems.Thm_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_x1
-- name    : ModularCurve.XOne.isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_x1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/df9faa48-52be-5c98-a364-0b9b93432d7c
-- title:
--   Discrete valuation ring at a closed point of X₁(M)
-- statement:
--   Let $p$ be a prime, let $M \ge 5$ with $p \nmid M$, and let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, with $\zeta \in L$ a primitive $p$-th root of unity. Let $K_1 \subseteq L((q))$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field $\mathtt{qExpFunctionFieldC}\ \mathbb{Q}\ \Gamma_1(M)$, i.e. $K_1 = \mathtt{laurentBaseChange}\ L\ (\mathtt{x1FunctionField}\ M)$. Let $A$ be a discrete valuation ring which is a domain with fraction field $L$, with $p \in \mathfrak{m}_A$, with $\zeta$ in the image of $A$, and with $\mathfrak{m}_A = (\varpi)$; $K_1$ carries a compatible $A$-algebra structure. Let $j \in K_1$ be nonzero with Laurent expansion the image of $\mathtt{jq} = q^{-1}\cdot \mathtt{jNumQ}$, and write $A_1 = \mathtt{chartAlgFin}\ A\ K_1\ j$ for the subalgebra of elements of $K_1$ integral over $A[j]$. Let $W_0$ be a valuation subring of $K_1$ consisting exactly of those $f$ admitting power series $x, y$ over $A$ with $y$ having nonzero reduction modulo $\mathfrak{m}_A$ and $f \cdot \tilde y = \tilde x$ in $L((q))$, and assume $A_1 \subseteq W_0$. Let $y$ be a point of $\operatorname{Spec} A_1$, i.e. a prime ideal, such that $\varpi \in y$, such that every element of $A_1$ lying in the non-units of $W_0$ lies in $y$, and such that some element of $y$ does not lie in the non-units of $W_0$. Finally let $R$ be the subring of the residue field of $W_0$ consisting exactly of those $e$ for which there are $s, t \in A_1$ with $t \notin y$ and $e \cdot \rho(t) = \rho(s)$, where $\rho$ denotes reduction from $W_0$ to its residue field. Then $R$ is a discrete valuation ring and the residue field of $W_0$ is a fraction field of $R$.
--
--   This is the good-level case $\Gamma = \Gamma_1(M)$ of a regularity statement for the two-chart integral model of the modular curve: the localisation of the finite chart ring at a closed point $y$ of the special fibre, realised inside the residue field of the Gauss valuation ring $W_0$, is a discrete valuation ring with that residue field as its fraction field. It is used to deduce the analogous statement for congruence subgroups lying between $\Gamma_1(M)$ and an intersection with a $\Gamma_0$-type group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_x1.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOne.isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀)

    (y : ↥(XFin A (↥K₁) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal)
    (hy𝔓 : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀.nonunits → s ∈ y.asIdeal)
    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K₁) j), s ∈ y.asIdeal ∧ (s : ↥K₁) ∉ W₀.nonunits)

    (R : Subring (IsLocalRing.ResidueField ↥W₀))
    (hR : ∀ e : IsLocalRing.ResidueField ↥W₀, e ∈ R ↔
      ∃ s t : ↥(chartAlgFin A (↥K₁) j), t ∉ y.asIdeal ∧
        e * IsLocalRing.residue ↥W₀ ⟨(t : ↥K₁), hSW₀ t⟩ = IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩) :
    IsDiscreteValuationRing ↥R ∧ IsFractionRing ↥R (IsLocalRing.ResidueField ↥W₀) := by sorry
