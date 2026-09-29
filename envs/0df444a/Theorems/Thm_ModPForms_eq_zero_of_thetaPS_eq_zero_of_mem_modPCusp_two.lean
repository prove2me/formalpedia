-- Prove2me | Theorems.Thm_ModPForms_eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two
-- name    : ModPForms.eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/12e4f2cd-7732-57c7-a37e-0b7ea447765b
-- title:
--   Theta operator is injective on weight-two mod p cusp forms
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $N$ be a positive integer with $p \nmid N$, and let $F$ be a field of characteristic $p$. Write $\mathrm{modPCusp}\,N\,2\,F$ for the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\sum_n \overline{a_n} q^n$ for which there exist a cusp form $f$ of weight $2$ on $\Gamma_0(N)$ and a sequence $a : \mathbb{N} \to \mathbb{Z}$ with $\mathrm{qCoeff}\,f\,n = a_n$ in $\mathbb{C}$ for all $n$ (the coefficients of the $q$-expansion of $f$ at $\infty$, taken with width $1$), the series being the coefficientwise image of $a$ in $F$. Let $\varphi \in F[[q]]$ belong to this span, and assume $\mathrm{thetaPS}\,\varphi = 0$, i.e. the power series whose $n$-th coefficient is $n$ times the $n$-th coefficient of $\varphi$ (the product taken in $F$) vanishes; equivalently, every coefficient of $\varphi$ in a degree prime to $p$ is zero. The conclusion is $\varphi = 0$.
--
--   This is the weight-two case of Katz's theorem on the operator $\theta = q\,d/dq$ acting on modular forms modulo $p$: a mod $p$ cusp form of weight two and level prime to $p$ annihilated by $\theta$ vanishes, for odd $p$. It is used in the analysis of integral $q$-expansion lattices and of Hecke operators on weight-two cusp forms away from $p = 2$, via [`CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two`](thm.html#CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two) and [`CuspForm.exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two`](thm.html#CuspForm.exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (F : Type) [Field F] [CharP F p]
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPCusp N 2 F) (hθ : ModPForms.thetaPS φ = 0) :
    φ = 0 := by sorry
