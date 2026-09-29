-- Prove2me | Theorems.Thm_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
-- name    : ModPForms.eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/b53e15f7-8b42-5849-9fa8-7ce5c49db8b4
-- title:
--   Reduced cusp forms with ψ(qᵖ) also reduced vanish
-- statement:
--   Let $p$ be a prime, let $N$ be a natural number with $p \nmid N$, let $k$ be an integer, and let $F$ be a field in which the image of $p$ is nonzero. Write $\mathrm{modPCusp}\,N\,k\,F$ for the $F$-submodule of $F[[q]]$ spanned by those power series of the form $\sum_n \bar a_n q^n$, where $a : \mathbb{N} \to \mathbb{Z}$ is an integer sequence, $f$ is a cusp form of weight $k$ on $\Gamma_0(N)$ whose $q$-expansion coefficients (the coefficients of `qExpansion 1 f`) satisfy $\mathrm{qCoeff}\,f\,n = a_n$ for every $n$, and $\bar a_n$ denotes the image of $a_n$ in $F$. Let $\psi \in F[[q]]$ lie in this span, and suppose moreover that the series whose $n$-th coefficient is the $(n/p)$-th coefficient of $\psi$ when $p \mid n$ and $0$ otherwise — that is, $\psi(q^p)$ — also lies in this span. Then $\psi = 0$.
--
--   The statement says that the span of the reductions of integral weight-$k$ cusp forms on $\Gamma_0(N)$, with $p$ invertible in the coefficient field, contains no nonzero series stable enough to admit its own $q^p$-expansion in the span; the operator involved is the classical $V_p$ occurring in the $q$-expansion identity $T_p = U_p + p^{k-1}V_p$ of Atkin and Lehner. It is used in the proofs of [`CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice`](thm.html#CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice) and [`CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two`](thm.html#CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two), which control integrality of $q$-coefficients under the Atkin–Lehner involutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModPForms.eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
    (p : ℕ) (hp : p.Prime) (N : ℕ) (hpN : ¬ p ∣ N) (k : ℤ)
    (F : Type) [Field F] (hpF : (p : F) ≠ 0)
    (ψ : PowerSeries F) (hψ : ψ ∈ ModPForms.modPCusp N k F)
    (hV : (PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) ψ else 0) ∈ ModPForms.modPCusp N k F) :
    ψ = 0 := by sorry
