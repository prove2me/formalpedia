-- Prove2me | Theorems.Thm_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match
-- name    : HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/52aefd8f-54ac-5cad-b491-341568959e53
-- title:
--   Structure constants lie in mathbb Z₍ₚ₎ for basis-matched mathbb Zₚ-models
-- statement:
--   Let $p$ be a prime, let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb Q$, and let $H_p$ be a commutative ring carrying a Hopf algebra structure over $\mathbb Z_p$. Suppose given an isomorphism $\varphi \colon \mathbb Q_p \otimes_{\mathbb Q} A \to \mathbb Q_p \otimes_{\mathbb Z_p} H_p$ of $\mathbb Q_p$-algebras which is compatible with all the remaining structure maps over $\mathbb Q_p$: the comultiplication of $\varphi(x)$ equals $(\varphi \otimes \varphi)$ applied to the comultiplication of $x$, the counit of $\varphi(x)$ equals that of $x$, and $\varphi$ commutes with the antipode, for every $x$. Suppose further that for some $n$ there are bases $b$ of $A$ over $\mathbb Q$ and $b^{H_p}$ of $H_p$ over $\mathbb Z_p$, both indexed by $\mathrm{Fin}\,n$, matched by $\varphi(1 \otimes b_i) = 1 \otimes b^{H_p}_i$ for all $i$. Then all five families of structure constants of $A$ in the basis $b$ lie in the image of the subring of rationals whose denominator is coprime to $p$, that is, in $\mathbb Z_{(p)} \subset \mathbb Q$: the multiplication constants $b.\mathrm{repr}(b_i b_j)_k$, the coordinates $b.\mathrm{repr}(1)_k$ of the unit, the coordinates of $\mathrm{comul}(b_i)$ in the basis $b \otimes b$ of $A \otimes_{\mathbb Q} A$ indexed by pairs, the counit values $\varepsilon(b_i)$, and the coordinates $b.\mathrm{repr}(S(b_i))_k$ of the antipode.
--
--   This is the integrality statement for a $\mathbb Q$-Hopf algebra admitting a $\mathbb Z_p$-model matched on bases: all structure constants are $p$-integral rationals. It is obtained from the characterisation of $\mathbb Z_{(p)} = \mathbb Q \cap \mathbb Z_p$ by the condition $\|q\|_p \le 1$, and is used by the variant [`HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic`](thm.html#HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic), where the counit and antipode compatibilities are derived rather than assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal TensorProduct
open scoped TensorProduct in

theorem HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x))
    (hφcounit : ∀ x, Coalgebra.counit (R := ℚ_[p]) (φ x) = Coalgebra.counit (R := ℚ_[p]) x)
    (hφanti : ∀ x, φ (HopfAlgebra.antipode ℚ_[p] x) = HopfAlgebra.antipode ℚ_[p] (φ x))
    (n : ℕ) (b : Module.Basis (Fin n) ℚ A) (bHp : Module.Basis (Fin n) ℤ_[p] Hp)
    (hmatch : ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i)) :
    (∀ i j k, b.repr (b i * b j) k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ k, b.repr 1 k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := ℚ) (b i)) jk
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i, Coalgebra.counit (R := ℚ) (b i) ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i k, b.repr (HopfAlgebra.antipode ℚ (b i)) k
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) := by sorry
