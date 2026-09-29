-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord
-- name    : ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9ec6ea2c-17ca-506e-9dbd-e7ea51d8c777
-- title:
--   Descent of p-divisible divisors along constant-field extensions
-- statement:
--   Fix a prime $p$, a finite-index subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix `ModularGroup.T`, an algebraically closed field $\kappa$ of characteristic $p$, and an algebraically closed field $K$ that is a $\kappa$-algebra. Write $F_\kappa =$ [`ModularCurve.qExpFunctionFieldC κ Γ`](def/ModularCurve_X1.html#L101) and $F_K =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate fields of $\kappa((q))$, respectively $K((q))$, generated over the constant field by the quotients $\mathrm{intSeriesC}\,p_f / \mathrm{intSeriesC}\,p_g$ of base-changed integral $q$-expansions $p_f, p_g$ of modular forms of some weight for $\Gamma$ (with $\mathrm{intSeriesC}\,p_g \ne 0$). The assertion is: for every $f \in F_K$ with $f \ne 0$ such that $p \mid \operatorname{ord}_v f$ for every place $v$ of $F_K$ over $K$ — a place being a proper valuation subring of $F_K$ containing $K$ whose ring is a principal ideal ring, and $\operatorname{ord}_v$ the associated normalised additive valuation — there exist $f_0 \in F_\kappa$ with $f_0 \ne 0$, elements $f_1, g \in F_K$ and $c \in K$ with $c \ne 0$, such that $p \mid \operatorname{ord}_{v_0} f_0$ for every place $v_0$ of $F_\kappa$ over $\kappa$, the Laurent series of $f_1$ is obtained from that of $f_0$ by applying $\kappa \to K$ to each coefficient (the map [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16)), and $f = c \cdot g^p \cdot f_1$ in $F_K$.
--
--   This is the function-field form of the rigidity of $p$-torsion in the Jacobian under enlargement of an algebraically closed base field: modulo $p$-th powers and constants, a function on the modular curve over $K$ whose divisor is divisible by $p$ already comes from the curve over the smaller algebraically closed field $\kappa$, equivalently every regular logarithmic differential descends. It feeds the analysis of Cartier-fixed regular differentials and Abel–Jacobi data on the modular curve used in the Raynaud-style argument for points of $X(\Gamma)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_eq_mul_pow_mul_of_coe_eq_coeffMap_of_forall_dvd_ord
    (p : ℕ) [Fact p.Prime]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra κ K] :
    ∀ f : ModularCurve.qExpFunctionFieldC K Γ, f ≠ 0 →
      (∀ v : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K Γ), (p : ℤ) ∣ v.ord f) →
      ∃ (f₀ : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f₁ : ModularCurve.qExpFunctionFieldC K Γ) (c : K) (g : ModularCurve.qExpFunctionFieldC K Γ),
        f₀ ≠ 0 ∧ c ≠ 0 ∧
        (∀ v₀ : AlgebraicCurve.Place κ (↥(ModularCurve.qExpFunctionFieldC κ Γ)), (p : ℤ) ∣ v₀.ord f₀) ∧
        ((f₁ : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) ((f₀ : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) : LaurentSeries κ) ∧
        f = algebraMap K (ModularCurve.qExpFunctionFieldC K Γ) c * g ^ p * f₁ := by sorry
