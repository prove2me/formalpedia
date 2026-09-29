-- Prove2me | Theorems.Thm_ModularCurve_XOne_isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits
-- name    : ModularCurve.XOne.isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/81a6c2a9-4ae1-5498-a258-502052fb9638
-- title:
--   Primes above the Gauss prime in the j-chart are maximal
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $5 \le M$ and $p \nmid M$, and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M) \cap \Gamma_0(p) \le \Gamma \le \Gamma_1(M)$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K_1$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of `qExpFunctionFieldC ℚ Γ`, the subfield of $\mathrm{LaurentSeries}\,\mathbb{Q}$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f/\mathrm{intSeriesC}\,\mathbb{Q}\,p_g$ attached to integral $q$-expansions of modular forms of level $\Gamma$ and equal weight. Let $A$ be a discrete valuation domain with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $\varpi$ a generator of the maximal ideal, and let $A \to K_1$ be an algebra structure compatible with $A \to L \to K_1$. Let $j \in K_1$ be nonzero with underlying Laurent series the coefficientwise image of `jq` (the $q$-expansion $q^{-1}\cdot\mathrm{jNumQ}$). Let $W_0$ be a valuation subring of $K_1$ characterised by: $f \in W_0$ iff there are power series $x, y$ over $A$ with the reduction of $y$ modulo the maximal ideal nonzero and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,L$ after pushing coefficients along $A \to L$; assume every element of the chart algebra $\mathrm{chartAlgFin}\,A\,K_1\,j$, the $A$-subalgebra of elements of $K_1$ integral over $A[j]$, lies in $W_0$. Let $y$ be a point of $\mathrm{Spec}$ of that chart algebra such that $\varpi$ lies in the prime $y$, every element of the chart algebra lying in the nonunits of $W_0$ lies in $y$, and some element of $y$ does not lie in the nonunits of $W_0$. Then the prime ideal of $y$ is maximal.
--
--   This is the dimension-theoretic step showing that a point of the $j$-finite chart of the integral two-chart model which lies in the special fibre (it contains $\varpi$) and strictly above the Gauss prime $\mathfrak{P}_0 = \mathrm{chartAlgFin}\,A\,K_1\,j \cap \mathfrak{m}_{W_0}$ is a closed point; the chart algebra is integral over $A[j]$ with $j$ transcendental over $A$, so its reduction along $\mathfrak{P}_0$ has Krull dimension one. It feeds the construction of the Gauss valuation subring and its residue field on the two-chart integral model of the modular curve for $\Gamma_1(M) \cap \Gamma_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOne_isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOne.isMaximal_asIdeal_of_forall_mem_nonunits_imp_mem_of_exists_not_mem_nonunits
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓle : Γ ≤ CongruenceSubgroup.Gamma1 M)
    (hΓge : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ Γ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
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
    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K₁) j), s ∈ y.asIdeal ∧ (s : ↥K₁) ∉ W₀.nonunits) :
    y.asIdeal.IsMaximal := by sorry
