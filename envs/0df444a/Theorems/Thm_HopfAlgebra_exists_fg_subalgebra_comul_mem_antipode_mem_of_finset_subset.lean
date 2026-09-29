-- Prove2me | Theorems.Thm_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
-- name    : HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/22beff54-11e2-58f5-aec6-480109254c0e
-- title:
--   Finitely generated Hopf subalgebras exhaust a Hopf subalgebra
-- statement:
--   Let $k$ be a field and $H$ a commutative ring carrying a Hopf algebra structure over $k$, and let $K$ be a $k$-subalgebra of $H$. Assume two closure conditions: for every $x \in K$ the comultiplication $\Delta(x) =$ `Coalgebra.comul x`$\in H \otimes_k H$ lies in the $k$-span of the set of elementary tensors $a \otimes b$ with $a, b \in K$; and for every $x \in K$ the antipode value `HopfAlgebra.antipode k x` again lies in $K$. Let $s$ be a finite subset of $H$ whose underlying set is contained in $K$. Then there is a $k$-subalgebra $K_0$ of $H$ with $K_0 \le K$, such that $K_0$ is finitely generated as a $k$-algebra (`Subalgebra.FG`), the set underlying $s$ is contained in $K_0$, every $x \in K_0$ has $\Delta(x)$ in the $k$-span of the elementary tensors $a \otimes b$ with $a, b \in K_0$, and the antipode maps $K_0$ into itself. Note that the comultiplication conditions are stated as membership in a span of elementary tensors rather than in the image of a tensor product of submodules.
--
--   This is the local finiteness statement for commutative Hopf algebras: a Hopf subalgebra of a commutative Hopf algebra over a field is the directed union of its finitely generated Hopf subalgebras, here in the form that any finite subset is contained in such a finitely generated piece. It is used in the proof of [`HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem`](thm.html#HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem), where a faithful flatness assertion for $K \subseteq H$ is reduced to the finitely generated case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (s : Finset H) (hs : (↑s : Set H) ⊆ K) :
    ∃ K₀ : Subalgebra k H, K₀ ≤ K ∧ K₀.FG ∧ (↑s : Set H) ⊆ K₀ ∧
      (∀ x ∈ K₀, Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K₀, ∃ b ∈ K₀, t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K₀, HopfAlgebra.antipode k x ∈ K₀) := by sorry
