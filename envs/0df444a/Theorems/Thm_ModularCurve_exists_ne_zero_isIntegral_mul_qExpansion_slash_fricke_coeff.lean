-- Prove2me | Theorems.Thm_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff
-- name    : ModularCurve.exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/db61366d-5d60-5588-b4a3-2ca7cbda626e
-- title:
--   Bounded denominators for the Fricke transform of a Γ₁(N)-form
-- statement:
--   Fix a natural number $N$ with $N \neq 0$ and an integer $k$, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_1(N)$, read as a subgroup of $\mathrm{GL}_2(\mathbb{R})$ in the sense of Mathlib's `CongruenceSubgroup.Gamma1`. Let $a$ be a natural number, and assume that for every $n \in \mathbb{N}$ the complex number $N^{a}$ times the $n$-th coefficient of the $q$-expansion of $f$ of width $1$ (that is, the Fourier expansion at $\infty$ in $q = e^{2\pi i \tau}$) is integral over $\mathbb{Z}$, i.e. an algebraic integer. Let $W \in \mathrm{GL}_2(\mathbb{R})$ be an element whose underlying $2 \times 2$ real matrix is the Fricke matrix $\begin{pmatrix} 0 & -1 \\ N & 0\end{pmatrix}$. Then there exists a natural number $D \neq 0$ such that for every $n \in \mathbb{N}$ the number $D$ times the $n$-th coefficient of the width-$1$ $q$-expansion of the function $f \mid_k W$, the weight-$k$ slash of the underlying function of $f$ by $W$, is integral over $\mathbb{Z}$. No relation between $D$ and $N$ or $a$ is asserted.
--
--   This is the qualitative half of the bounded-denominator ($q$-expansion rationality) principle for the Fricke involution: integrality of the Fourier coefficients of $f$ at $\infty$, up to a fixed power of $N$, forces the coefficients of $f \mid_k W$ to have a common denominator. It feeds the quantitative refinement [`ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff`](thm.html#ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff), in which the denominator is taken to be a power of the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff (N : ℕ)
    [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (a : ℕ)
    (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
      (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ)).coeff n))
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ n : ℕ, IsIntegral ℤ ((D : ℂ) *
      (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n) := by sorry
