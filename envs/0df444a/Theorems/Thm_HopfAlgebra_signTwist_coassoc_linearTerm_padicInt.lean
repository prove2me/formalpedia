-- Prove2me | Theorems.Thm_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt
-- name    : HopfAlgebra.signTwist_coassoc_linearTerm_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/df8ec5a6-3a53-55c8-bdb5-46c689bf0ac1
-- title:
--   Linear term in coassociativity of the sign-twisted comultiplication
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $d_0 \in \mathbb{Z}_p$ be a unit, and let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ whose comultiplication is cocommutative, i.e. $\mathrm{Coalgebra.IsCocomm}\ \mathbb{Z}_p\ H$ holds. Write $\iota = \mathrm{HopfAlgebra.antipode}\ \mathbb{Z}_p$ for the antipode, $\Delta = \mathrm{Coalgebra.comul} : H \to H \otimes_{\mathbb{Z}_p} H$ for the comultiplication, and set $P_- := \mathrm{Ring.inverse}(2) \cdot (\mathrm{id} - \iota)$ as a $\mathbb{Z}_p$-linear endomorphism of $H$ (since $p$ is odd, $2$ is invertible in $\mathbb{Z}_p$ and the ring inverse is a genuine inverse), $Q := P_- \otimes P_-$ on $H \otimes_{\mathbb{Z}_p} H$, and $A : (H \otimes H) \otimes H \xrightarrow{\sim} H \otimes (H \otimes H)$ for the associator of the tensor product. The assertion is that for every $a \in H$,
--   $$A\bigl(((Q \circ \Delta) \otimes \mathrm{id}_H)(\Delta a)\bigr) + A\bigl((\Delta \otimes \mathrm{id}_H)(Q(\Delta a))\bigr) = (\mathrm{id}_H \otimes (Q \circ \Delta))(\Delta a) + (\mathrm{id}_H \otimes \Delta)(Q(\Delta a)),$$
--   an identity in $H \otimes_{\mathbb{Z}_p} (H \otimes_{\mathbb{Z}_p} H)$.
--
--   This is the coefficient of $(d_0^{-1}-1)$ in the coassociativity of the sign-twisted comultiplication $\Delta' = \Delta + (d_0^{-1}-1)\,Q \circ \Delta$ on a cocommutative commutative Hopf algebra over $\mathbb{Z}_p$ with $p$ odd, the remaining obligation once the constant term (ordinary coassociativity) and the quadratic term are dealt with. It is used by [`HopfAlgebra.signTwist_comul_coassoc_padicInt`](thm.html#HopfAlgebra.signTwist_comul_coassoc_padicInt), and the argument rests on the involutivity of the antipode and on its compatibility with $\Delta$ in the cocommutative case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open scoped TensorProduct in

theorem HopfAlgebra.signTwist_coassoc_linearTerm_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Q := TensorProduct.map Pm Pm
    let Δ : H →ₗ[ℤ_[p]] H ⊗[ℤ_[p]] H := Coalgebra.comul
    let A := (TensorProduct.assoc ℤ_[p] H H H).toLinearMap
    ∀ a : H,
      A ((LinearMap.rTensor H (Q.comp Δ)) (Δ a)) + A ((LinearMap.rTensor H Δ) (Q (Δ a)))
      = (LinearMap.lTensor H (Q.comp Δ)) (Δ a) + (LinearMap.lTensor H Δ) (Q (Δ a)) := by sorry
