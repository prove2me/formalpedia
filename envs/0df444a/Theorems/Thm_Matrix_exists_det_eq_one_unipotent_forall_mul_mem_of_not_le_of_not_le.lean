-- Prove2me | Theorems.Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le
-- name    : Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/9845aaa5-1f1c-5bab-b740-835cae752d52
-- title:
--   Unipotent in SL₂(F) stabilising I₀ and mapping I into I'
-- statement:
--   Let $F$ be a field and let $I_0, I, I'$ be submodules of the ring $M_2(F)$ of $2\times 2$ matrices over $F$ regarded as a left module over itself, i.e. left ideals of $M_2(F)$. Assume that $I$ is neither the zero ideal nor all of $M_2(F)$, that likewise $I'$ is neither zero nor all of $M_2(F)$, and that $I_0$ is contained in neither $I$ nor $I'$. Then there exists a matrix $g \in M_2(F)$ with $\det g = 1$ and $(g-1)^2 = 0$ (so $g$ is unipotent of order dividing the square of a transvection) such that right multiplication by $g$ preserves $I_0$ and carries $I$ into $I'$: for every $A \in I_0$ one has $Ag \in I_0$, and for every $A \in I$ one has $Ag \in I'$. No hypothesis is imposed on $I_0$ beyond the two non-containments, and, unlike the lemma [`Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top`](thm.html#Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top) on which the proof rests, the conclusion here does not assert $g \neq 1$.
--
--   Since the proper non-zero left ideals of $M_2(F)$ are the annihilators of non-zero column vectors, this is the statement that the unipotent elements of $\mathrm{SL}_2(F)$ fixing a prescribed line (or, when $I_0 = M_2(F)$, with no constraint at all) act transitively enough to move one line to another; the matrix produced is a transvection or the identity. It is used in the construction of elements of prescribed reduced norm in an Eichler order, in the lemma [`QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le
    {F : Type*} [Field F] (I₀ I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤)
    (h₀ : ¬ I₀ ≤ I) (h₀' : ¬ I₀ ≤ I') :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧
      (∀ A ∈ I₀, A * g ∈ I₀) ∧ ∀ A ∈ I, A * g ∈ I' := by sorry
