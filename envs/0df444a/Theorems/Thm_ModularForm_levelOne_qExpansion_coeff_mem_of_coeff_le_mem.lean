-- Prove2me | Theorems.Thm_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem
-- name    : ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/2a0b08dd-2bdf-59a7-a2e5-63ee9034316d
-- title:
--   Level-one forms of weight 12N: first N+1 coefficients determine integrality
-- statement:
--   Let $N$ be a natural number, let $F$ be a modular form of weight $12N$ for $\mathrm{SL}_2(\mathbb{Z})$ (the weight entering as the integer $12\cdot N$), and let $R$ be a subring of $\mathbb{C}$. Write $\sum_{n\ge 0} a_n q^n$ for the $q$-expansion of $F$ at the cusp with respect to the period $1$, i.e. the power series $\mathrm{qExpansion}\ 1$ attached to the underlying function $F \colon \mathbb{H} \to \mathbb{C}$. The hypothesis is that $a_n \in R$ for every $n \le N$. The conclusion is that, for the given natural number $n$, the coefficient $a_n$ lies in $R$; since $n$ is universally quantified, this says that all Fourier coefficients of $F$ lie in $R$. No condition is imposed on $R$ beyond being a subring of $\mathbb{C}$ (so it contains $1$, hence $\mathbb{Z}$), and the case $N = 0$ is included, where the hypothesis on $a_0$ alone forces every coefficient to lie in $R$.
--
--   This is the standard integrality statement for level-one forms: in weight $12N$ the space has dimension $N+1$ with a basis $E_4^{3i}\Delta^{N-i}$ of forms with integral $q$-expansions, so the first $N+1$ coefficients control the whole expansion. It is used, via [`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`](thm.html#ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary), in the control of Fourier coefficients of forms under the slash action; the proof invokes the expression of the $q$-expansion of $F$ as $P(E_4^3/\Delta)\cdot\Delta^N$ with $\deg P \le N$, together with the integrality of the $q$-expansions of $E_4$ and of $\Delta = q\cdot(\text{unit})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_levelOne_qExpansion_coeff_mem_of_coeff_le_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups in

theorem ModularForm.levelOne_qExpansion_coeff_mem_of_coeff_le_mem (N : ℕ)
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) (R : Subring ℂ)
    (hF : ∀ n ≤ N, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R) (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ R := by sorry
