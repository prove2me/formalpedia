-- Prove2me | Theorems.Thm_ModularCurve_qExpansion_slash_coeff_mem_range_of_isIntegralQExp
-- name    : ModularCurve.qExpansion_slash_coeff_mem_range_of_isIntegralQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/07df4a52-8293-50b8-94e8-d798a1bbb89c
-- title:
--   Algebraicity of q-expansion coefficients of F∣_kγ
-- statement:
--   Let $L$ be a nonzero natural number and $k$ an integer, and let $F$ be a modular form of weight $k$ for the image of $\Gamma_1(L)$ in $\mathrm{GL}_2(\mathbb{R})$. Assume $F$ has integral $q$-expansion in the sense of the project predicate [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37): there is a power series $r$ over $\mathbb{Z}$ whose coefficientwise image under $\mathbb{Z}\to\mathbb{C}$ equals the width-one $q$-expansion of $F$, i.e. `UpperHalfPlane.qExpansion 1 F`. Let $\iota$ be a ring homomorphism from `AlgebraicClosure ℚ` to $\mathbb{C}$, let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, and let $n$ be a natural number. Then the $n$-th coefficient of the width-$L$ $q$-expansion of the weight-$k$ slash $F \mid_k \gamma$ (the function on the upper half-plane underlying $F$, slashed by $\gamma$, expanded in $q_L = e^{2\pi i \tau / L}$) lies in the range of $\iota$. Equivalently, each such coefficient is an algebraic number; no statement is made about which number field it generates, in particular nothing about $\mathbb{Q}(\zeta_L)$.
--
--   This is the algebraicity half of the classical statement that the Fourier coefficients of an integral modular form at all the cusps are algebraic numbers (classically they lie in $\mathbb{Q}(\zeta_L)$). It feeds the construction of the $\overline{\mathbb{Q}}$-rational structure on spaces of modular forms used downstream, being cited by [`ModularForm.exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq`](thm.html#ModularForm.exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansion_slash_coeff_mem_range_of_isIntegralQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.qExpansion_slash_coeff_mem_range_of_isIntegralQExp
    (L : ℕ) [NeZero L] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 L : Subgroup (GL (Fin 2) ℝ)) k)
    {r : PowerSeries ℤ} (hF : ModularCurve.IsIntegralQExp F r)
    (ι : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) (n : ℕ) :
    (UpperHalfPlane.qExpansion L ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n ∈ Set.range ι := by sorry
