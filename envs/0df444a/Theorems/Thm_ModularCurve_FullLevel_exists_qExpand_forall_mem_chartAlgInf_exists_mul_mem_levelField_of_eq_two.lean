-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_two
-- name    : ModularCurve.FullLevel.exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/1dd70951-a41b-5008-8117-9f78d0085716
-- title:
--   Pole charts of j and j(q^q) compare, case q=2
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'\ge 1$ with $q\nmid M'$, and assume $\overline{\mathbb{Q}}$-base change of the full level-$M'$ modular function field is contained in $F:=$ `fieldBar q M'`, the $\overline{\mathbb{Q}}$-base change (inside $\overline{\mathbb{Q}}((q))$, via coefficientwise extension `coeffEmb`) of the function field of $X_H(q^2M')$ for $H=\ker\big((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\big)$. Let $k_0\subseteq\overline{\mathbb{Q}}$, let $K_1$ be a finite extension of $k_0$ inside $\overline{\mathbb{Q}}$, and let $A_1$ be a valuation subring of $K_1$; give $F$ its $k_0$-algebra structure through the constants. Let $F_0$ be a $k_0$-intermediate field of $F$ such that: the compositum of $F_0$ with the image of $\overline{\mathbb{Q}}$ is all of $F$; $F_0$ is stable under every `levelAutBar q M' ζ' γ` for $\zeta'$ a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ and $\gamma\in\Gamma_0(M')$; for every finite extension $K'$ of $k_0$ in $\overline{\mathbb{Q}}$, any $K'$-linearly independent family $c_1,\dots,c_m\in\overline{\mathbb{Q}}$ and any $a_1,\dots,a_m$ in $T':=k_0(K')\cdot F_0$ with $\sum_i c_ia_i=0$ force all $a_i=0$; and every element of $F$ whose Laurent series has rational coefficients lies in $F_0$. Put $T_1:=k_0(K_1)\cdot F_0\subseteq F$, equipped with an $A_1$-algebra structure whose structure map agrees with the inclusion of constants $A_1\subseteq K_1\subseteq\overline{\mathbb{Q}}\to F$. Let $j_1\in T_1$ be nonzero with Laurent series `coeffEmb` of `jq`. Then there is $j'\in T_1$ with Laurent series `coeffEmb (qExpand ℚ q jq)`, i.e. the series of $j$ with exponents scaled by $q$, such that, writing $B$ and $B'$ for the integral closures of $A_1[j_1^{-1}]$ and of $A_1[j'^{-1}]$ in $T_1$ (the pole-chart algebras `chartAlgInf`), every $y\in B'$ admits $s=1+j_1^{-1}a$ with $a,s\in B$ and $sy\in B$, and every $y\in B$ admits $s=1+j'^{-1}a$ with $a,s\in B'$ and $sy\in B'$.
--
--   This is the comparison, over the level field $T_1=K_1\cdot F_0$, of the two pole charts of the two-chart integral models attached to the modular invariant $j$ and to $j(q^q)$: each chart algebra is carried into the other after multiplication by a unit congruent to $1$ modulo the uniformiser $j^{-1}$ at the cusp, the classical integrality and symmetry of the modular equation $\Phi_q$ in the shape needed for the integral models. It is the $q=2$ form of the statement, and is used in the analysis of the descent and of the level-automorphism action on the two-chart integral model at $q=2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve CongruenceSubgroup
open ModularCurve
open ModularCurve.FullLevel
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_qExpand_forall_mem_chartAlgInf_exists_mul_mem_levelField_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →
    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],
    ∃ j' : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀),
      ((j' : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) ∧
      (∀ y, y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' →
        ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ∧
          (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ ∧ s = 1 + j₁⁻¹ * a) ∧
          s * y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∧
      (∀ y, y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ →
        ∃ s, s ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' ∧
          (∃ a, a ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j' ∧ s = 1 + j'⁻¹ * a) ∧
          s * y ∈ TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j') := by sorry
