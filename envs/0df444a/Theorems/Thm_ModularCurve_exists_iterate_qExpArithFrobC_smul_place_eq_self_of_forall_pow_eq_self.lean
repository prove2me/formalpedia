-- Prove2me | Theorems.Thm_ModularCurve_exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self
-- name    : ModularCurve.exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/1d6eefb1-afc0-5fb5-a70a-8ba011ac45a2
-- title:
--   Places of q-expansion function fields are Frobenius-periodic
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$ with the property that every $a \in K$ satisfies $a^{p^n} = a$ for some $n > 0$ (so $K$ is algebraic over $\mathbb{F}_p$), and let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $\mathrm{T}$. Write $F =$ `qExpFunctionFieldC K Γ` for the intermediate field of the field of formal Laurent series over $K$ generated over $K$ by the set `intFormRatiosC K Γ` of quotients $\iota_K(p_f)/\iota_K(p_g)$, where $f, g$ are modular forms of some common weight $k$ for $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb{R})$) whose $q$-expansions are given by integral power series $p_f, p_g$ via `IsIntegralQExp`, $\iota_K$ denotes coefficientwise base change of an integral series to $K$, and $\iota_K(p_g) \ne 0$. Let $w$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. The assertion is that there exists $j > 0$ with $\sigma^j \cdot w = w$, where $\sigma =$ `qExpArithFrobC p K Γ` is the semilinear automorphism of $F$ over $K$ given by the pair consisting of the coefficientwise $p$-power Frobenius of $F$ and the $p$-power Frobenius of $K$, acting on places of $F$ over $K$ by the pointwise action.
--
--   In geometric terms, a closed point of the modular curve attached to $\Gamma$ over an algebraic closure of $\mathbb{F}_p$ is already defined over a finite subfield, so the orbits of the arithmetic Frobenius on places of the function field are finite. The result is used by [`ModularCurve.exists_iterate_qExpFrobeniusPushforwardModL_eq_self_of_forall_pow_eq_self`](thm.html#ModularCurve.exists_iterate_qExpFrobeniusPushforwardModL_eq_self_of_forall_pow_eq_self), where periodicity of places under Frobenius is needed to compare places with their Frobenius translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_iterate_qExpArithFrobC_smul_place_eq_self_of_forall_pow_eq_self
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ)) :
    ∃ j : ℕ, 0 < j ∧ (fun v : Place K ↥(qExpFunctionFieldC K Γ) => qExpArithFrobC p K Γ • v)^[j] w = w := by sorry
