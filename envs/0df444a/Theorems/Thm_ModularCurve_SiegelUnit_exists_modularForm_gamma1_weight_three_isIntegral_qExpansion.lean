-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
-- name    : ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/bd8b1886-08a0-558c-9455-0c0314b392db
-- title:
--   A weight-three form on Γ₁(N) with N-integral expansions at ∞ and 0
-- statement:
--   Let $N$ be a natural number with $3 \le N$, and regard the congruence subgroup $\Gamma_1(N)$ as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. The assertion is that there exist a modular form $E$ of weight $3$ for $\Gamma_1(N)$ and a single natural number $a$ such that the following four conditions hold simultaneously for that pair. First, for every $n \in \mathbb{N}$, the number $N^a$ times the $n$-th coefficient of the $q$-expansion of $E$ of width $1$ (Fourier expansion in $q = e^{2\pi i \tau}$) is integral over $\mathbb{Z}$. Second, the coefficient of index $0$ of that width-$1$ expansion is nonzero. Third, $N^a$ times the inverse of this constant coefficient is integral over $\mathbb{Z}$. Fourth, for every $n \in \mathbb{N}$, the number $N^a$ times the $n$-th coefficient of the width-$N$ $q$-expansion (in $e^{2\pi i \tau/N}$) of the weight-$3$ slash $E \mid_{[3]} S$, where $S = \begin{pmatrix} 0 & -1 \\ 1 & 0\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ is viewed in $\mathrm{GL}_2(\mathbb{R})$, is integral over $\mathbb{Z}$. Thus one exponent $a$ works at once for the expansions at the cusps $\infty$ and $0$ and for the inverse of the constant term at $\infty$.
--
--   This provides a weight-three Eisenstein anchor on $\Gamma_1(N)$ for $N \ge 3$: a form whose Fourier coefficients at the cusps $\infty$ and $0$ become algebraic integers after clearing a fixed power of $N$, and whose constant term at $\infty$ is an invertible such quantity; the candidate is the Eisenstein series $G_3$ of level $N$ attached to the vector $(0,1)$ modulo $N$, whose coefficients are computed by [`EisensteinSeries.qExpansion_eisensteinG_coeff`](thm.html#EisensteinSeries.qExpansion_eisensteinG_coeff) and whose constant term is the partial zeta value $\sum_{d \equiv 1 \ (N)} d^{-3}$. It is used by [`ModularCurve.exists_gamma1_peaked_auxiliary_form`](thm.html#ModularCurve.exists_gamma1_peaked_auxiliary_form) in the construction of auxiliary forms with prescribed behaviour at the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_weight_three_isIntegral_qExpansion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion
    (N : ℕ) (hN : 3 ≤ N) :
    ∃ (E : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) 3) (a : ℕ),
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff n)) ∧
      (UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0 ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by sorry
