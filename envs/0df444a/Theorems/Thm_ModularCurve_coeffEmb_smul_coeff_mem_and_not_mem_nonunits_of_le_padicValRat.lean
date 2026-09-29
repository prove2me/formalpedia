-- Prove2me | Theorems.Thm_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
-- name    : ModularCurve.coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/7f176eb4-94e9-5255-ab7c-93ae23df0064
-- title:
--   Uniform p-adic normalisation of a rational Laurent q-expansion
-- statement:
--   Let $K$ be a field of characteristic zero and $A \subseteq K$ a valuation subring, let $p$ be a prime number, and assume that $A$ lies over $p$ in the sense that the image of $p$ in $K$ belongs to `A.nonunits`, the set of non-units of $A$ (equivalently, the maximal ideal of $A$). Let $g$ be a Laurent series with rational coefficients and let $n$ be an integer such that $n \le v_p(g_k)$ for every index $k \in \mathbb{Z}$ with $g_k \neq 0$, where $v_p$ denotes `padicValRat p`; suppose furthermore that some index $k_0$ satisfies $g_{k_0} \neq 0$ and $v_p(g_{k_0}) = n$. Form the rescaled series $(p^n)^{-1} \cdot g$ over $\mathbb{Q}$ and push its coefficients into $K$ along the structure map $\mathbb{Q} \to K$, that is, apply the coefficientwise ring homomorphism `coeffEmb K`. The conclusion is twofold: every coefficient of the resulting Laurent series over $K$ lies in $A$, and its $k_0$-th coefficient does not lie in `A.nonunits`, i.e. it is a unit of $A$.
--
--   This is the rescaling of a $q$-expansion with rational coefficients by the power of $p$ given by its $p$-adic content, in the form that is uniform in the valuation ring $A$ above $p$: one and the same rational constant $p^{-n}$ makes the expansion integral with at least one unit coefficient, simultaneously for all such $A$. It is the arithmetic input used when a rational modular function is read as a unit of a Gauss-type valuation ring at a cusp, and is cited throughout the development of charts and Hasse-type exponents for multiplicative coverings of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
    {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K)
    {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (g : LaurentSeries ℚ) (n : ℤ)
    (hle : ∀ k : ℤ, g.coeff k ≠ 0 → n ≤ padicValRat p (g.coeff k))
    (k₀ : ℤ) (hk₀ : g.coeff k₀ ≠ 0) (hk₀n : padicValRat p (g.coeff k₀) = n) :
    (∀ k : ℤ, (coeffEmb K (((p : ℚ) ^ n)⁻¹ • g)).coeff k ∈ A) ∧
      (coeffEmb K (((p : ℚ) ^ n)⁻¹ • g)).coeff k₀ ∉ A.nonunits := by sorry
