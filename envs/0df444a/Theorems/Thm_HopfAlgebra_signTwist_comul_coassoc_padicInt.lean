-- Prove2me | Theorems.Thm_HopfAlgebra_signTwist_comul_coassoc_padicInt
-- name    : HopfAlgebra.signTwist_comul_coassoc_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/db3d6256-a461-5e7d-9d1b-20b4c4b0f678
-- title:
--   Coassociativity of the sign-twisted comultiplication over ℤₚ
-- statement:
--   Let $p$ be a natural number that is prime (as a `Fact` instance) with $p \neq 2$, let $d_0 \in \mathbb{Z}_p$ be a unit, and let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ whose comultiplication is cocommutative, i.e. `Coalgebra.IsCocomm ℤ_[p] H` holds. Write $\iota$ for the antipode `HopfAlgebra.antipode ℤ_[p]` and $\Delta$ for `Coalgebra.comul`, and introduce the $\mathbb{Z}_p$-linear endomorphism $P_- := 2^{-1}\,(\mathrm{id} - \iota)$ of $H$, the scalar $2^{-1}$ being `Ring.inverse (2 : ℤ_[p])`, together with the twisted comultiplication $$\Delta' := \Delta + (d_0^{-1} - 1)\,\bigl((P_- \otimes P_-) \circ \Delta\bigr) : H \to H \otimes_{\mathbb{Z}_p} H,$$ where $d_0^{-1}$ is `Ring.inverse d₀`. The assertion is the equality of $\mathbb{Z}_p$-linear maps $H \to H \otimes_{\mathbb{Z}_p} H \otimes_{\mathbb{Z}_p} H$ obtained by applying $\Delta'$, then $\Delta' \otimes \mathrm{id}_H$ (i.e. `LinearMap.rTensor H Δ'`), then the associator `TensorProduct.assoc ℤ_[p] H H H`, with the map obtained by applying $\Delta'$ and then $\mathrm{id}_H \otimes \Delta'$ (i.e. `LinearMap.lTensor H Δ'`). In other words, $\Delta'$ is again coassociative.
--
--   This is the coassociativity axiom for the sign twist of a cocommutative commutative Hopf algebra over $\mathbb{Z}_p$ by a unit $d_0$, one of the Hopf-algebra identities needed in the quadratic-twist construction; it is used by [`HopfAlgebra.exists_signTwist_linearEquiv_padicInt_of_odd`](thm.html#HopfAlgebra.exists_signTwist_linearEquiv_padicInt_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_signTwist_comul_coassoc_padicInt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open scoped TensorProduct in

theorem HopfAlgebra.signTwist_comul_coassoc_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Δ' : H →ₗ[ℤ_[p]] (H ⊗[ℤ_[p]] H) :=
      Coalgebra.comul + (Ring.inverse d₀ - 1) • ((TensorProduct.map Pm Pm).comp Coalgebra.comul)
    ↑(TensorProduct.assoc ℤ_[p] H H H) ∘ₗ LinearMap.rTensor H Δ' ∘ₗ Δ'
      = LinearMap.lTensor H Δ' ∘ₗ Δ' := by sorry
