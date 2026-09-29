-- Prove2me | Theorems.Thm_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
-- name    : ModularForm.exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/46846468-3f02-5cb2-a526-b37ad207bd75
-- title:
--   Rational level-one forms are isobaric polynomials in E₄, E₆
-- statement:
--   Let $k$ be an integer and let $f$ be a modular form of weight $k$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$. Suppose $T \in \mathbb{Q}[[q]]$ is a power series with rational coefficients whose image under the map $\mathbb{Q} \to \mathbb{C}$ on coefficients is the $q$-expansion of $f$ of period $1$ at the cusp $\infty$. Then there exists a polynomial $\Phi \in \mathbb{Q}[X_0, X_1]$ in two variables which is weighted homogeneous of degree `k.toNat` for the weights $4$ on $X_0$ and $6$ on $X_1$ (so every monomial $X_0^{a}X_1^{b}$ occurring in $\Phi$ satisfies $4a + 6b = k$ when $k \ge 0$, the weight being recorded as the natural number `k.toNat`), such that substituting for $X_0$ and $X_1$ the two rational power series obtained by mapping $\mathbb{Z} \to \mathbb{Q}$ on the coefficients of $$1 + \sum_{n \ge 1}\Bigl(240\sum_{d \mid n} d^3\Bigr)q^n \quad\text{and}\quad 1 + \sum_{n \ge 1}\Bigl(-504\sum_{d \mid n} d^5\Bigr)q^n,$$ that is, the $q$-expansions of $E_4$ and $E_6$, yields exactly $T$.
--
--   This is the rational form of the classical structure theorem for level-one modular forms, $M_k(\mathrm{SL}_2(\mathbb{Z})) = \mathbb{C}[E_4,E_6]_k$: a form whose expansion at $\infty$ has rational coefficients is an isobaric polynomial in $E_4$ and $E_6$ with rational coefficients. It is used by [`ModularForm.exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two`](thm.html#ModularForm.exists_mvPolynomial_levelOne_relation_qExpansion_gamma0_of_weight_two), and the proof appeals to the computations of the $q$-expansions of $E_4$ and $E_6$ in [`ModularCurve.qExpansion_E4_eq_map_eisenstein4`](thm.html#ModularCurve.qExpansion_E4_eq_map_eisenstein4) and [`ModularCurve.qExpansion_E6_eq_map_mk`](thm.html#ModularCurve.qExpansion_E6_eq_map_mk).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_isWeightedHomogeneous_aeval_eq_of_map_eq_qExpansion_levelOne
    {k : ℤ} (f : ModularForm 𝒮ℒ k) (T : PowerSeries ℚ)
    (hT : T.map (algebraMap ℚ ℂ) = qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) ℚ,
      Φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) k.toNat ∧
        MvPolynomial.aeval
            (![(PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3).map
                (Int.castRingHom ℚ),
              (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5).map
                (Int.castRingHom ℚ)] : Fin 2 → PowerSeries ℚ) Φ = T := by sorry
