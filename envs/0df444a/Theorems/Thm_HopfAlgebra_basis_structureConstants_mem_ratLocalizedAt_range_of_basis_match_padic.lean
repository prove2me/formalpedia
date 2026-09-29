-- Prove2me | Theorems.Thm_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
-- name    : HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/61a33b4f-ddb8-5e80-a9f2-023c4c784eff
-- title:
--   Integrality of structure constants from a basis-matched p-adic model
-- statement:
--   Let $p$ be a prime, let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Q}$, and let $H_p$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$. Suppose given an isomorphism of $\mathbb{Q}_p$-algebras $\varphi \colon \mathbb{Q}_p \otimes_{\mathbb{Q}} A \to \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H_p$ which is compatible with comultiplication in the sense that $\mathrm{comul}(\varphi x) = (\varphi \otimes \varphi)(\mathrm{comul}\, x)$ for all $x$, the comultiplications being taken over $\mathbb{Q}_p$. Suppose further given $n \in \mathbb{N}$, a basis $b$ of $A$ over $\mathbb{Q}$ indexed by $\mathrm{Fin}\,n$, a basis $b^{H_p}$ of $H_p$ over $\mathbb{Z}_p$ indexed by the same set, matched by $\varphi(1 \otimes b_i) = 1 \otimes b^{H_p}_i$ for all $i$. Then all five families of structure constants of the Hopf $\mathbb{Q}$-algebra $A$ in the basis $b$ lie in the image in $\mathbb{Q}$ of the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of those rationals whose denominator is coprime to $p$ (that is, in $\mathbb{Z}_{(p)}$): the coordinates $b.\mathrm{repr}(b_i b_j)_k$ of products, the coordinates $b.\mathrm{repr}(1)_k$ of the unit, the coordinates of $\mathrm{comul}(b_i)$ over $\mathbb{Q}$ in the tensor-product basis $b \otimes b$, the counit values $\varepsilon(b_i)$, and the coordinates $b.\mathrm{repr}(S(b_i))_k$ of the antipode.
--
--   The statement expresses the elementary integrality principle $\mathbb{Q} \cap \mathbb{Z}_p = \mathbb{Z}_{(p)}$ at the level of Hopf-algebra structure constants: a $\mathbb{Z}_p$-model of $A$ whose basis matches a given $\mathbb{Q}$-basis forces all constants to be $p$-integral. It is used to produce a finite flat Hopf order over $\mathbb{Z}_{(p)}$ inside $A$, in [`HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match`](thm.html#HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_basis_match).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal TensorProduct
open scoped TensorProduct in

theorem HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_basis_match_padic
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (Hp : Type) [CommRing Hp] [HopfAlgebra ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₐ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp))
    (hφcomul : ∀ x, Coalgebra.comul (R := ℚ_[p]) (φ x) =
        (TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := ℚ_[p]) x))
    (n : ℕ) (b : Module.Basis (Fin n) ℚ A) (bHp : Module.Basis (Fin n) ℤ_[p] Hp)
    (hmatch : ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i)) :
    (∀ i j k, b.repr (b i * b j) k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ k, b.repr 1 k ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := ℚ) (b i)) jk
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i, Coalgebra.counit (R := ℚ) (b i) ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) ∧
    (∀ i k, b.repr (HopfAlgebra.antipode ℚ (b i)) k
        ∈ (algebraMap (GaloisRep.ratLocalizedAt p) ℚ).range) := by sorry
