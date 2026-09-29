-- Prove2me | Theorems.Thm_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit
-- name    : HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/5417f9b9-b642-5b1b-8ea5-849610c3722e
-- title:
--   Freeness over a Hopf subalgebra with nilpotent augmentation ideal
-- statement:
--   Let $k$ be a field and let $H$ be a commutative ring carrying the structure of a Hopf algebra over $k$, with comultiplication $\Delta$, counit $\varepsilon$ and antipode $S$. Let $K$ be a $k$-subalgebra of $H$ subject to three conditions. First, for every $x \in K$ the element $\Delta(x)$ of $H \otimes_k H$ lies in the $k$-span of the set of tensors $a \otimes b$ with $a \in K$ and $b \in K$; this is the formal expression of $\Delta(K) \subseteq K \otimes_k K$. Second, $S(x) \in K$ for every $x \in K$. Third, the kernel of the ring homomorphism obtained by composing the inclusion $K \hookrightarrow H$ with the counit algebra map $\varepsilon \colon H \to k$ — that is, the augmentation ideal $K^{+} = \ker(\varepsilon|_{K})$ of $K$ — is a nilpotent ideal, so $(K^{+})^{n} = 0$ for some $n$. The conclusion is that $H$, viewed as a module over the subalgebra $K$, is free. No finiteness hypothesis is imposed on $H$ or on $K$.
--
--   This is the infinitesimal case of the freeness (and hence faithful flatness) of a commutative Hopf algebra over a Hopf subalgebra, the first step of Milne's proof of the quotient theorem for affine group schemes, the model case being $K = k[t]/(t^p)$. Here it feeds the passage from freeness in the nilpotent case to faithful flatness of $H$ over a Hopf subalgebra under reducedness hypotheses over a perfect field; the proof uses the $H$-algebra isomorphism $H \otimes_K H \cong H \otimes_k (H/K^{+}H)$ provided by [`HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span`](thm.html#HopfAlgebra.exists_algEquiv_subalgebraTensor_tensorQuotient_of_comul_mem_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_free_subalgebra_of_isNilpotent_ker_counit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.free_subalgebra_of_isNilpotent_ker_counit
    {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H)
    (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ K, HopfAlgebra.antipode k x ∈ K)
    (hnil : IsNilpotent (RingHom.ker ((Bialgebra.counitAlgHom k H).comp K.val))) :
    Module.Free ↥K H := by sorry
