-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
-- name    : Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/39b885f2-273b-5ce1-a125-5b167c725b00
-- title:
--   Effective descent along an idempotent Amitsur cocycle
-- statement:
--   Let $R \to A$ be a homomorphism of commutative rings (in the same universe) making $A$ a faithfully flat $R$-module, and let $G$ be a finite additive commutative group. Let $e : G \to A \otimes_R A$ be a family of elements of $A \otimes_R A$ indexed by $G$ which forms a complete orthogonal family of idempotents (`CompleteOrthogonalIdempotents e`: each $e_i$ is idempotent, $e_i e_j = 0$ for $i \neq j$, and $\sum_{i} e_i = 1$), and assume the Amitsur cocycle identity: for every $k \in G$, $\sum_{i \in G} c_{12}(e_i)\, c_{23}(e_{k-i}) = c_{13}(e_k)$, the product being taken in the target of the three coface homomorphisms `c₁₂ R A`, `c₂₃ R A`, `c₁₃ R A` out of $A \otimes_R A$ provided by `Algebra.DescentCofaces`. The conclusion asserts the existence of an $R$-submodule $M$ of the $R$-module $G \to A$ of $A$-valued functions on $G$ such that, first, a function $f : G \to A$ lies in $M$ precisely when $\sum_{m \in G} e_m \cdot (f(k-m) \otimes 1) = 1 \otimes f(k)$ in $A \otimes_R A$ for all $k \in G$, and, second, the inclusion $M \hookrightarrow (G \to A)$ is a base change along $R \to A$, i.e. the induced $A$-linear map $A \otimes_R M \to (G \to A)$ is an isomorphism.
--
--   This is effective faithfully flat descent in the affine case, applied to the descent datum on the free module $A^G$ given by translation of indices weighted by the idempotents $e_m$: the Amitsur cocycle identity is exactly the cocycle condition for that datum, and $M$ is its module of invariants, a twisted form of $R^G$. It is used by [`Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary`](thm.html#Algebra.DescentCofaces.exists_finite_flat_unramified_nonempty_ringHom_iff_isCoboundary), where such idempotent cocycles encode $G$-torsors and the descended module carries the structure of a finite flat unramified $R$-algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.lean

import Mathlib
import Definitions.Def_Algebra_DescentCofaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Algebra.DescentCofaces
open scoped TensorProduct

universe u v

theorem Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (hcoc : ∀ k, ∑ i, (c₁₂ R A).hom (e i) * (c₂₃ R A).hom (e (k - i)) = (c₁₃ R A).hom (e k)) :
    ∃ M : Submodule R (G → A),
      (∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[R] 1) = 1 ⊗ₜ[R] f k) ∧
      IsBaseChange A M.subtype := by sorry
