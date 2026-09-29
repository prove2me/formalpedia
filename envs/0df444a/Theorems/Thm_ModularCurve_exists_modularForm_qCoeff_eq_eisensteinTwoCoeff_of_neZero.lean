-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero
-- name    : ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/e22c8250-3afa-522b-bf8d-eba716aad77a
-- title:
--   Weight-two Eisenstein form on Γ₀(N) with prescribed q-coefficients
-- statement:
--   Let $N$ be a natural number, assumed non-zero. The assertion is that there exists a holomorphic modular form $E$ of weight $2$ for the congruence subgroup $\Gamma_0(N)$ (Mathlib's `CongruenceSubgroup.Gamma0 N`) whose $q$-expansion coefficients are prescribed integers: for every natural number $n$, the $n$-th coefficient of the $q$-expansion of $E$ of width $1$, namely [`ModularFormClass.qCoeff E n`](def/FLTPrelim_Modularity.html#L19) $=$ the coefficient of $q^n$ in `qExpansion 1 E`, equals the image in $\mathbb{C}$ of the integer `eisensteinTwoCoeff N n`, which by definition is $N-1$ when $n=0$ and is $24\,\sigma'_N(n)$ otherwise, where $\sigma'_N(n)=\sum_{d\mid n,\ N\nmid d} d$ is the sum of those positive divisors of $n$ that are not divisible by $N$. Thus the form has $q$-expansion $(N-1)+24\sum_{n\ge 1}\sigma'_N(n)q^n$ at the cusp $\infty$. No claim is made about the behaviour of $E$ at the other cusps beyond what membership in the space of weight-two holomorphic modular forms on $\Gamma_0(N)$ entails, and no uniqueness is asserted; for $N=1$ all the prescribed coefficients vanish, so the statement is then satisfied by the zero form.
--
--   This is the classical fact that, although the weight-two Eisenstein series $E_2$ is only quasi-modular, the combination $N\,E_2(N\tau)-E_2(\tau)$ is a genuine holomorphic modular form of weight $2$ on $\Gamma_0(N)$, with the stated $q$-expansion at $\infty$. It supplies the Eisenstein element used by [`CuspForm.exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral`](thm.html#CuspForm.exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral), where a form with integral $q$-coefficients congruent to the prescribed ones is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_modularForm_qCoeff_eq_eisensteinTwoCoeff_of_neZero (N : ℕ) [NeZero N] :
    ∃ E : ModularForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ n : ℕ, ModularFormClass.qCoeff E n = (eisensteinTwoCoeff N n : ℂ) := by sorry
