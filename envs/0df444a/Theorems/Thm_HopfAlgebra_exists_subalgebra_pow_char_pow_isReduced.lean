-- Prove2me | Theorems.Thm_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced
-- name    : HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/06e5488a-ae92-5164-8401-602cdc19c89c
-- title:
--   Frobenius image of a finitely generated Hopf subalgebra is reduced
-- statement:
--   Let $k$ be a perfect field which is of characteristic $p$ for a prime $p$, let $H$ be a commutative ring carrying a Hopf algebra structure over $k$, and let $K$ be a $k$-subalgebra of $H$ satisfying: for every $x \in K$ the comultiplication $\Delta(x) =$ `Coalgebra.comul` $x$ lies in the $k$-submodule of $H \otimes_k H$ spanned by the tensors $a \otimes_k b$ with $a, b \in K$; for every $x \in K$ the antipode value $S(x)$ again lies in $K$; and $K$ is finitely generated as a $k$-algebra (`K.FG`). Then there are a natural number $r$ and a $k$-subalgebra $K'$ of $H$ such that $K' \le K$, $K'$ is finitely generated, the ring $K'$ is reduced (`IsReduced`), the underlying subset of $K'$ in $H$ is exactly $\{\,x^{p^r} : x \in K\,\}$, every $x \in K'$ has $\Delta(x)$ in the $k$-span of the tensors $a \otimes_k b$ with $a, b \in K'$, and $S(x) \in K'$ for every $x \in K'$. The $\Delta$-stability is thus stated in the span form rather than as an inclusion $\Delta(K') \subseteq K' \otimes_k K'$ of an image of a tensor product.
--
--   This is the statement that for a finitely generated Hopf subalgebra over a perfect field of characteristic $p$ the Frobenius image $K^{p^r}$ is again a $\Delta$- and $S$-stable finitely generated subalgebra, and is reduced once $p^r$ exceeds the nilpotency index of the nilradical. It is used in [`HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField`](thm.html#HopfAlgebra.faithfullyFlat_subalgebra_of_forall_isReduced_of_perfectField), where the reduced case of faithful flatness of Hopf subalgebras is bootstrapped to the general one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_subalgebra_pow_char_pow_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.exists_subalgebra_pow_char_pow_isReduced
    {k : Type u} [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K) (hfg : K.FG) :
    ∃ (r : ℕ) (K' : Subalgebra k H), K' ≤ K ∧ K'.FG ∧ IsReduced ↥K' ∧
      (K' : Set H) = {y : H | ∃ x ∈ K, y = x ^ p ^ r} ∧
      (∀ x ∈ K', Coalgebra.comul (R := k) x ∈
        Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K', ∃ b ∈ K', t = a ⊗ₜ[k] b}) ∧
      (∀ x ∈ K', HopfAlgebra.antipode k x ∈ K') := by sorry
