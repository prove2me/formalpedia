-- Prove2me | Theorems.Thm_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card
-- name    : Matrix.bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/c0d9f836-8b00-556c-a118-14ae40e1e9a7
-- title:
--   Cyclic vectors for a division algebra in M_N(K)
-- statement:
--   Let $K$ be a field and $D$ a ring carrying a $K$-algebra structure in which every non-zero element is a unit, and let $N$ be a non-empty finite index type with $\dim_K D = \#N$. Let $\iota : D \to M_N(K)$ be a $K$-algebra homomorphism and let $e_0 : N \to K$ be a non-zero vector. The conclusion is a conjunction. First, the map $d \mapsto \iota(d)\,e_0$ (matrix–vector multiplication, `Matrix.mulVec`) is a bijection from $D$ onto $K^N$; that is, $e_0$ is a cyclic vector for $\iota$ and the orbit map is also injective. Second, for every matrix $T \in M_N(K)$ satisfying $T\,\iota(d) = \iota(d)\,T$ for all $d \in D$, there exists $\xi \in D$ such that $T\,(\iota(d)\,e_0) = \iota(d\xi)\,e_0$ for all $d \in D$; in the coordinates supplied by the bijection, $T$ acts as right multiplication by $\xi$. No separability, centrality or finite-dimensionality hypothesis on $D$ beyond the equality of $\dim_K D$ with $\#N$ is imposed.
--
--   This is the concrete form of the double-centraliser statement for a division algebra $D$ of degree $\#N$ embedded in $M_N(K)$: such an embedding makes $K^N$ a one-dimensional free $D$-module, and the commutant of $\iota(D)$ consists of the right multiplications by elements of $D$. It is used in the comparison of local boxes attached to maximal orders in a quaternion algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card
    {K : Type} [Field K] {D : Type} [Ring D] [Algebra K D]
    (hdiv : ∀ d : D, d ≠ 0 → IsUnit d)
    {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
    (hdim : Module.finrank K D = Fintype.card N)
    (ι : D →ₐ[K] Matrix N N K) (e₀ : N → K) (he₀ : e₀ ≠ 0) :
    Function.Bijective (fun d : D => (ι d).mulVec e₀) ∧
      ∀ T : Matrix N N K, (∀ d : D, T * ι d = ι d * T) →
        ∃ ξ : D, ∀ d : D, T.mulVec ((ι d).mulVec e₀) = (ι (d * ξ)).mulVec e₀ := by sorry
