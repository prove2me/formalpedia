-- Prove2me | Theorems.Thm_IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement
-- name    : IsLocalRing.exists_separabilityElement_residueField_tensor_of_separabilityElement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/7286a9fe-4664-57e1-b7ee-6b426085bdca
-- title:
--   Separability elements descend to the residue field
-- statement:
--   Let $S$ be a commutative local ring and let $\Lambda$ be a (not necessarily commutative) ring, so that $S \otimes_{\mathbb Z} \Lambda$ is an $S$-algebra. Suppose given an element $e$ of $(S \otimes_{\mathbb Z} \Lambda) \otimes_S (S \otimes_{\mathbb Z} \Lambda)$ such that, first, the multiplication map `LinearMap.mul'` of the $S$-algebra $S \otimes_{\mathbb Z} \Lambda$ carries $e$ to $1$, and second, for every $x \in S \otimes_{\mathbb Z} \Lambda$ the endomorphism of the relative tensor square obtained by applying left multiplication by $x$ in the first factor and the identity in the second agrees on $e$ with the one obtained by applying the identity in the first factor and right multiplication by $x$ in the second; that is, $(x \otimes 1)e = e(1 \otimes x)$. The conclusion asserts the existence of an element $e_\Lambda$ of $(\kappa \otimes_{\mathbb Z} \Lambda) \otimes_{\kappa} (\kappa \otimes_{\mathbb Z} \Lambda)$, where $\kappa =$ `IsLocalRing.ResidueField S` is the residue field of $S$, satisfying the same two conditions over $\kappa$: the multiplication map of the $\kappa$-algebra $\kappa \otimes_{\mathbb Z} \Lambda$ sends $e_\Lambda$ to $1$, and $(x \otimes 1)e_\Lambda = e_\Lambda(1 \otimes x)$ for all $x \in \kappa \otimes_{\mathbb Z} \Lambda$.
--
--   The two conditions on $e$ are the classical requirements for a separability element of the $S$-algebra $S \otimes_{\mathbb Z} \Lambda$, and the statement is the stability of their existence under the base change $S \to \kappa$ along the residue map. It is used in the deformation-theoretic part of the argument, where a separability element over the residue field is produced from one over the coefficient ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_separabilityElement_residueField_tensor_of_separabilityElement.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalRing.exists_separabilityElement_residueField_tensor_of_separabilityElement
    (S : Type) [CommRing S] [IsLocalRing S] {Λ : Type} [Ring Λ]
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e) :
    ∃ eΛ : ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ) ⊗[(IsLocalRing.ResidueField S)] ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ),
      LinearMap.mul' (IsLocalRing.ResidueField S) ((IsLocalRing.ResidueField S) ⊗[ℤ] Λ) eΛ = 1 ∧
      ∀ x : (IsLocalRing.ResidueField S) ⊗[ℤ] Λ,
        TensorProduct.map (LinearMap.mulLeft (IsLocalRing.ResidueField S) x) LinearMap.id eΛ =
          TensorProduct.map LinearMap.id (LinearMap.mulRight (IsLocalRing.ResidueField S) x) eΛ := by sorry
