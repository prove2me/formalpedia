-- Prove2me | Theorems.Thm_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt
-- name    : HopfAlgebra.signTwist_galois_of_formula_of_linearEquiv_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/548621b2-53ee-500a-b6e9-1fa04dc40235
-- title:
--   Sign-twisted Galois equivariance of the twist bijection
-- statement:
--   Let $p$ be an odd prime, let $d \in \mathbb{Q}_p$ and let $s$ be an element of $\overline{\mathbb{Q}_p} =$ `AlgebraicClosure ℚ_[p]` with $s \neq 0$ and $s^2 = d$ (the image of $d$ under the structure map). Let $H$ and $H'$ be commutative rings carrying $\mathbb{Z}_p$-Hopf algebra structures, with the comultiplication of $H$ cocommutative, and let $e \colon H' \to H$ be a $\mathbb{Z}_p$-linear isomorphism. Write $\mathrm{Pt}(H) =$ `WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])` for the $\overline{\mathbb{Q}_p}$-points of $H$ regarded as a monoid under convolution, and similarly for $H'$. Let $\beta \colon \mathrm{Pt}(H') \to \mathrm{Pt}(H)$ be a bijection of the underlying types which is given by the formula $(\beta \varphi')(h) = \varphi'(e^{-1}(h - P_-h)) + s^{-1}\,\varphi'(e^{-1}(P_-h))$ for all $\varphi'$ and all $h \in H$, where $P_- = \tfrac12(\mathrm{id} - S)$ with $S$ the antipode of $H$ and $\tfrac12$ the ring inverse of $2$ in $\mathbb{Z}_p$. The conclusion: for every $\mathbb{Q}_p$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}_p}$, all points $f', g' \in \mathrm{Pt}(H')$ and $g \in \mathrm{Pt}(H)$ with $g'(h') = \sigma(f'(h'))$ for all $h' \in H'$ and $g(h) = \sigma((\beta f')(h))$ for all $h \in H$, one has: if $\sigma s = s$ then $\beta g' = g$, and if $\sigma s \neq s$ then $\beta g' \cdot g = 1$ in the convolution monoid $\mathrm{Pt}(H)$.
--
--   This is the Galois-equivariance property of the quadratic sign twist: the bijection $\beta$ on $\overline{\mathbb{Q}_p}$-points defined by the half-sum/half-difference formula intertwines the Galois action up to the quadratic character cut out by $s$, so that $\sigma$ acts on the twisted points through $\beta$ when $\sigma$ fixes $s$ and through $\beta$ composed with inversion when it does not. It feeds [`HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt`](thm.html#HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt), where the twisted point functor is compared with the untwisted one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped TensorProduct in

theorem HopfAlgebra.signTwist_galois_of_formula_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (s : AlgebraicClosure ℚ_[p]) (hs0 : s ≠ 0)
    (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (e : H' ≃ₗ[ℤ_[p]] H)
    (β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
         WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
    (hβ : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ (φ' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) (h : H),
        (β φ') h = φ' (e.symm (h - Pm h)) + s⁻¹ * φ' (e.symm (Pm h))) :
    ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
      (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ h' : H', g' h' = σ (f' h')) →
      (∀ h : H, g h = σ ((β f') h)) →
        (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by sorry
