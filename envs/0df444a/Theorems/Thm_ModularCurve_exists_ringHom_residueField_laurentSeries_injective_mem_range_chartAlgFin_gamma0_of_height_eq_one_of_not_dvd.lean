-- Prove2me | Theorems.Thm_ModularCurve_exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
-- name    : ModularCurve.exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f12188e0-ad9a-52e7-8bea-675dd4a24c3c
-- title:
--   Reduced q-expansions embed the residue field at a vertical prime
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$. Let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, and let $K_0$ be an intermediate field of $L \subseteq L(\!(q)\!)$ (Laurent series over $L$) which equals [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the field generated over $L$ inside $L(\!(q)\!)$ by the coefficientwise image under $\mathbb{Q} \to L$ of the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC ℚ (Gamma0 M')`. Let $A$ be a discrete valuation ring which is an $A$-algebra subring of $L$ with $L$ as fraction field, such that the image of $q$ lies in the maximal ideal of $A$, and assume $K_0$ is an $A$-algebra compatibly with $L$. Let $j_0 \in K_0$ be a nonzero element whose image in $L(\!(q)\!)$ is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), the $q$-expansion $q^{-1}\cdot(\text{jNum})$ of $j$ with coefficients pushed into $L$, and let $\varpi$ generate the maximal ideal of $A$. Write $B_0 =$ `chartAlgFin A K₀ j₀` for the subalgebra of elements of $K_0$ integral over $A[j_0]$. Let $\mathfrak{Q} \subseteq B_0$ be a prime ideal of height $1$ containing the image of $\varpi$. Then there is an injective ring homomorphism $\Theta$ from the residue field of $\mathfrak{Q}$ to $\kappa(A)(\!(q)\!)$, where $\kappa(A)$ is the residue field of $A$, such that: for every $a \in A$, $\Theta$ sends the class of $a$ in $B_0/\mathfrak{Q}$ to the constant Laurent series given by the residue of $a$; $\Theta$ sends the class of $j_0 \in B_0$ (the element `jChartFin A K₀ j₀`) to [`ModularCurve.jqModC (κ(A))`](def/ModularCurve_JqCoeff.html#L15), the reduction $q^{-1}\cdot(\text{jNum mod } \mathfrak{m}_A)$ of the $q$-expansion of $j$; and [`ModularCurve.jqNModC (κ(A)) M'`](def/ModularCurve_JqCoeff.html#L18), the series obtained from it by $q \mapsto q^{M'}$, lies in the range of $\Theta$.
--
--   This is the $q$-expansion principle for the $j$-finite chart of $X_0(M')$ at a prime of residue characteristic $q$ not dividing the level: elements of the integral chart are read as $A$-integral Laurent series, and reducing coefficients identifies the residue field at the vertical height-one prime with a subfield of $\kappa(A)(\!(q)\!)$ in which the reductions of $j(q)$ and $j(q^{M'})$ both lie. It is used in the separability statement for that residue field, where the two named elements provide the degree bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.exists_ringHom_residueField_laurentSeries_injective_mem_range_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1)
    (hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∈ 𝔔)
    :
    ∃ Θ : 𝔔.ResidueField →+* LaurentSeries (IsLocalRing.ResidueField A),
      Function.Injective Θ ∧
      (∀ a : A, Θ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) a)) =
        algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a)) ∧
      Θ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔.ResidueField (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀)) =
        ModularCurve.jqModC (IsLocalRing.ResidueField A) ∧
      ∃ z : 𝔔.ResidueField, Θ z = ModularCurve.jqNModC (IsLocalRing.ResidueField A) M' := by sorry
