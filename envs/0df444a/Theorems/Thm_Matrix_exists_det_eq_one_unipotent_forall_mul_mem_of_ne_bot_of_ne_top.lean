-- Prove2me | Theorems.Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
-- name    : Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/b3ef3760-c9d6-5745-adfa-4a7ccdd101a9
-- title:
--   A non-trivial unipotent in SL₂(F) carrying I into I'
-- statement:
--   Let $F$ be a field and let $I$ and $I'$ be two submodules of $M_2(F)$ regarded as a module over the ring $M_2(F)$ acting by left multiplication, i.e. two left ideals of the $2\times 2$ matrix ring over $F$. Assume that each is neither the zero ideal nor the whole ring: $I \ne \bot$, $I \ne \top$, $I' \ne \bot$, $I' \ne \top$ (so both are proper non-zero, hence minimal, left ideals). Then there exists a matrix $g \in M_2(F)$ with the following four properties: $\det g = 1$; $(g - 1)(g - 1) = 0$, so that $g$ is unipotent with $(g-1)^2 = 0$; $g \ne 1$; and $A g \in I'$ for every $A \in I$, i.e. right multiplication by $g$ carries $I$ into $I'$. Note that the containment $I g \subseteq I'$ is asserted in this one direction only, and that $g$ is produced as a single matrix of determinant one rather than as an element of any named subgroup.
--
--   The statement records that a non-trivial transvection of $SL_2(F)$ can be chosen to move any given proper non-zero left ideal of $M_2(F)$ into any other, reflecting the transitivity of $SL_2(F)$ on the lines of $F^2$ under the correspondence between minimal left ideals and annihilators of non-zero vectors. It is used in the variant for ideals merely not contained in one another, and in the construction of elements of reduced norm one in maximal and Eichler orders of quaternion algebras with prescribed multiplicative behaviour on level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
    {F : Type*} [Field F] (I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧ g ≠ 1 ∧ ∀ A ∈ I, A * g ∈ I' := by sorry
