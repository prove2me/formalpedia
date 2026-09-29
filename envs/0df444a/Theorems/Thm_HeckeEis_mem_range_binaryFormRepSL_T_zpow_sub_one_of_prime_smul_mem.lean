-- Prove2me | Theorems.Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem
-- name    : HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/3f7f2cc8-fd1e-5ebe-b28c-14583f04a731
-- title:
--   p-saturation of the image of T^h-1 on integral binary forms
-- statement:
--   Fix a natural number $n$ and a prime $p$ with $n < p$, and let $h \in \mathbb{Z}$ be an integer not divisible by $p$. Let [`HeckeEis.BinaryForm ℤ n`](def/HeckeEis_BinaryFormRep.html#L25) be the $\mathbb{Z}$-submodule of $\mathbb{Z}[X_0,X_1]$ (polynomials in `Fin 2` variables) of forms homogeneous of degree $n$, and let [`HeckeEis.binaryFormRepSL ℤ n`](def/HeckeEis_BinaryFormRep.html#L61) be the representation of $\mathrm{SL}(2,\mathbb{Z})$ on this submodule obtained by restricting the substitution algebra endomorphism $X_j \mapsto \sum_i M_{ij} X_i$ attached to the matrix $M$. For $M = T^h$, where $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$ is `ModularGroup.T`, this operator is $P(X_0,X_1) \mapsto P(X_0, hX_0 + X_1)$. The assertion is: if $v$ is an element of [`HeckeEis.BinaryForm ℤ n`](def/HeckeEis_BinaryFormRep.html#L25) such that $p \cdot v$ lies in the range of the $\mathbb{Z}$-linear endomorphism $\rho(T^h) - 1$ of that submodule, then $v$ itself lies in the range of $\rho(T^h) - 1$.
--
--   Equivalently, for $p > n$ and $p \nmid h$ the cokernel of $T^h - 1$ on the integral binary forms of degree $n$ (the symmetric power $\mathrm{Sym}^n \mathbb{Z}^2$) has no $p$-torsion; the elementary divisors of the torsion of this cokernel divide $n!\,h^n$, which is prime to $p$. It is used in the integral study of parabolic cohomology classes with coefficients in these symmetric powers, being cited by [`HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero`](thm.html#HeckeEis.exists_eq_prime_smul_of_coeffH1par_map_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem (n : ℕ) {p : ℕ} (hp : p.Prime) (hn : n < p)
    {h : ℤ} (hph : ¬ (p : ℤ) ∣ h) (v : ↥(HeckeEis.BinaryForm ℤ n))
    (hv : (p : ℤ) • v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1)) :
    v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1) := by sorry
