-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq
-- name    : FullLevelTate.exists_linearEquiv_cancelBaseChange_of_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/c5f0a259-f4db-5e64-b1cd-937784c68fe9
-- title:
--   Comparing base changes of a ℤ_λ-module to K
-- statement:
--   Let $\lambda$ be a prime, let $O'$ be a commutative ring carrying a $\mathbb{Z}_\lambda$-algebra structure, and let $K$ be a commutative ring carrying both an $O'$-algebra structure and a $\mathbb{Q}_\lambda$-algebra structure. Assume the two structure maps agree on $\mathbb{Z}_\lambda$, in the sense that for every $z \in \mathbb{Z}_\lambda$ the image of $z$ under $\mathbb{Z}_\lambda \to O' \to K$ equals the image of $z$ under $\mathbb{Z}_\lambda \hookrightarrow \mathbb{Q}_\lambda \to K$. Let $T$ be an additive commutative monoid equipped with a $\mathbb{Z}_\lambda$-module structure. Then there exists a $K$-linear isomorphism
--   $$e : K \otimes_{O'} (O' \otimes_{\mathbb{Z}_\lambda} T) \;\xrightarrow{\ \sim\ }\; K \otimes_{\mathbb{Q}_\lambda} (\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T)$$
--   such that for all $c \in K$, $a \in O'$ and $x \in T$ one has $e\bigl(c \otimes (a \otimes x)\bigr) = \bigl(\iota(a)\,c\bigr) \otimes (1 \otimes x)$, where $\iota : O' \to K$ is the structure map. Thus the isomorphism is pinned down on pure tensors, not merely asserted to exist.
--
--   This is the comparison of the two ways of inflating a $\mathbb{Z}_\lambda$-module $T$ to $K$, through $O'$ or through $\mathbb{Q}_\lambda$; both are canonically $K \otimes_{\mathbb{Z}_\lambda} T$. It is used in the treatment of full level structures at $\lambda$, where Tate-module constructions over a ring of integers $O'$ must be compared with their rational counterparts over $\mathbb{Q}_\lambda$, for the cases $\lambda = 2$, $\lambda = 3$ and $\lambda \geq 5$ separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq.lean

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearEquiv_cancelBaseChange_of_algebraMap_eq
    (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (K : Type) [CommRing K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    (T : Type) [AddCommMonoid T] [Module ℤ_[lam] T] :
    ∃ e : K ⊗[O'] (O' ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℚ_[lam]] (ℚ_[lam] ⊗[ℤ_[lam]] T),
      ∀ (c : K) (a : O') (x : T),
        e (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) = (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) := by sorry
