-- Prove2me | Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
-- name    : HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/15234b73-475e-5ecd-b4a6-6d0616c2fc9a
-- title:
--   Takeuchi's theorem: faithful flatness over a Hopf subalgebra
-- statement:
--   Let $k$ be a field and let $H$ be a commutative ring carrying a Hopf algebra structure over $k$ which is of finite type as a $k$-algebra. Let $K$ be a $k$-subalgebra of $H$ subject to two closure conditions: first, for every $x \in K$ the comultiplication $\Delta(x) \in H \otimes_k H$ lies in the $k$-submodule spanned by the elementary tensors $a \otimes_k b$ with $a, b \in K$ — that is, $\Delta(K)$ is contained in the image of $K \otimes_k K$ inside $H \otimes_k H$; second, the antipode of $H$ maps $K$ into itself, i.e. $S(x) \in K$ for every $x \in K$. (No counit condition is imposed separately, $K$ being a subalgebra.) The conclusion is that $H$, viewed as a module over the subalgebra $K$, is faithfully flat: flat, and such that tensoring with $H$ takes no nonzero $K$-module to zero.
--
--   This is Takeuchi's theorem in the finite-type case: a commutative Hopf algebra of finite type over a field is faithfully flat over each of its Hopf subalgebras, equivalently a surjection of affine algebraic groups over a field is faithfully flat. It is the field-level input for the faithful flatness statements about Hopf algebras and Cartier duals used elsewhere in the development, being cited by [`HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing`](thm.html#HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing) and by results on Witt-vector coordinates of Cartier duals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open scoped TensorProduct in

theorem HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) :
    Module.FaithfullyFlat ↥K H := by sorry
