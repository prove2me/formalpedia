-- Prove2me | Theorems.Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul
-- name    : ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/a769f48a-f454-5c49-a847-afeb9586a563
-- title:
--   A weight-one form on Γ₁(3) with Fricke eigenvalue -i/√3
-- statement:
--   The assertion is the existence of a modular form $g$ of weight $1$ for the congruence subgroup $\Gamma_1(3)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, with three properties. First, the $q$-expansion of $g$ in weight $1$ at the cusp $\infty$ has rational coefficients: for every natural number $n$ there is a rational number $r$ with the $n$-th coefficient of `UpperHalfPlane.qExpansion 1 g` equal to the image of $r$ in $\mathbb{C}$. Second, the coefficient of index $0$ of this expansion is $1$. Third, for every element $W$ of $\mathrm{GL}_2(\mathbb{R})$ whose underlying $2\times 2$ real matrix is the Fricke matrix $\begin{pmatrix}0&-1\\3&0\end{pmatrix}$, the weight-$1$ slash action of $W$ on the function $\mathbb{H}\to\mathbb{C}$ underlying $g$ equals the scalar multiple of that function by $-i/\sqrt{3}$; the quantification over $W$ is over all units of the matrix ring with that prescribed matrix, so the identity holds for the Fricke involution however it is presented as an element of $\mathrm{GL}_2(\mathbb{R})$.
--
--   The form produced is the theta series of the hexagonal lattice, equivalently the weight-one Eisenstein series attached to the pair of characters $(\mathbf 1,\chi_{-3})$, whose functional equation under $\tau\mapsto -1/(3\tau)$ is Poisson summation for the Eisenstein norm form $m^2+mn+n^2$. It is used by [`ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0`](thm.html#ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0), where a weight-one form with rational expansion, constant term $1$ and prescribed Fricke eigenvalue serves as a normalising factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in

theorem ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)) 1,
      (∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 g).coeff n = (r : ℂ)) ∧
      (UpperHalfPlane.qExpansion 1 g).coeff 0 = 1 ∧
      ∀ W : GL (Fin 2) ℝ, (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; 3, 0] →
        (⇑g : UpperHalfPlane → ℂ) ∣[(1 : ℤ)] W =
          (-Complex.I / (Real.sqrt 3 : ℂ)) • (⇑g : UpperHalfPlane → ℂ) := by sorry
