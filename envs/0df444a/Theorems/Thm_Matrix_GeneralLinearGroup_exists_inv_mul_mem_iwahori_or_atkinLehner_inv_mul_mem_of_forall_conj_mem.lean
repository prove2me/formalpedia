-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem
-- name    : Matrix.GeneralLinearGroup.exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/febbd5f8-9b6c-55e7-9396-cbd02da83e88
-- title:
--   Semi-normaliser of the Iwahori order in GL₂(K)
-- statement:
--   Let $K$ be a field, $O \subseteq K$ a valuation subring, and $\varpi \in K$ an element with $\varpi \in O$ and $\varpi \neq 0$. Write $\mathrm{Iw}$ for the set of $2\times 2$ matrices $M$ over $K$ all of whose entries lie in $O$ and which satisfy $\varpi^{-1}M_{10} \in O$ (rows and columns indexed by $\{0,1\}$, so $M_{10}$ is the lower-left entry). Let $g \in \mathrm{GL}_2(K)$ be such that for every matrix $M$ in $\mathrm{Iw}$ the conjugate $g M g^{-1}$ again lies in $\mathrm{Iw}$, i.e. all its entries lie in $O$ and $\varpi^{-1}$ times its lower-left entry lies in $O$. The conclusion asserts the existence of a unit $c \in K^\times$ for which one of two alternatives holds: either the entrywise scalar multiple $c^{-1}g$ and the entrywise scalar multiple $c\,g^{-1}$ both lie in $\mathrm{Iw}$ (entries in $O$, and $\varpi^{-1}$ times the lower-left entry in $O$, for each of the two matrices); or the matrix products $\bigl(\begin{smallmatrix} 0 & \varpi^{-1} \\ 1 & 0\end{smallmatrix}\bigr)\cdot(c^{-1}\cdot g)$ and $(c\cdot g^{-1})\cdot\bigl(\begin{smallmatrix} 0 & 1 \\ \varpi & 0\end{smallmatrix}\bigr)$ both lie in $\mathrm{Iw}$ in the same entrywise sense. All memberships are spelled out entrywise, and the hypothesis on $g$ is the single inclusion $g\,\mathrm{Iw}\,g^{-1} \subseteq \mathrm{Iw}$.
--
--   This is the local computation identifying the semi-normaliser $\{g \in \mathrm{GL}_2(K) : g\,\mathrm{Iw}\,g^{-1} \subseteq \mathrm{Iw}\}$ of the Iwahori order of level $\varpi$ with $K^\times\bigl(\mathrm{Iw}^\times \cup w_0\,\mathrm{Iw}^\times\bigr)$, where $w_0 = \bigl(\begin{smallmatrix} 0 & 1 \\ \varpi & 0\end{smallmatrix}\bigr)$ is the Atkin–Lehner element; no discreteness of the valuation is assumed and $\varpi$ may be a unit, in which case $\mathrm{Iw}$ is the full matrix ring over $O$. It is used in the count of points of the quotient by an Eichler order level structure with squarefree level, in [`QuaternionAlgebra.IsEichlerOrder.natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree`](thm.html#QuaternionAlgebra.IsEichlerOrder.natCard_setOf_exists_quotientMk_stabilizer_localBox_levelU_eq_of_dvd_of_squarefree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem
    {K : Type*} [Field K] (O : ValuationSubring K) (ϖ : K) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (g : GL (Fin 2) K)
    (hg : ∀ M : Matrix (Fin 2) (Fin 2) K, (∀ i j, M i j ∈ O) → ϖ⁻¹ * M 1 0 ∈ O →
      (∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i j ∈ O) ∧
        ϖ⁻¹ * ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 0 ∈ O) :
    ∃ c : Kˣ,
      ((∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
        ϖ⁻¹ * (((c⁻¹ : Kˣ) : K) * (g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ O ∧
        (∀ i j, (c : K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
        ϖ⁻¹ * ((c : K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ O) ∨
      ((∀ i j, ((!![0, ϖ⁻¹; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
          (((c⁻¹ : Kˣ) : K) • (g : Matrix (Fin 2) (Fin 2) K))) i j ∈ O) ∧
        ϖ⁻¹ * ((!![0, ϖ⁻¹; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
          (((c⁻¹ : Kˣ) : K) • (g : Matrix (Fin 2) (Fin 2) K))) 1 0 ∈ O ∧
        (∀ i j, (((c : K) • ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          (!![0, 1; ϖ, 0] : Matrix (Fin 2) (Fin 2) K)) i j ∈ O) ∧
        ϖ⁻¹ * ((((c : K) • ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          (!![0, 1; ϖ, 0] : Matrix (Fin 2) (Fin 2) K)) 1 0) ∈ O) := by sorry
