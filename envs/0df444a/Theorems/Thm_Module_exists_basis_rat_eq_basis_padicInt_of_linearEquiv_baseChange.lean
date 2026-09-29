-- Prove2me | Theorems.Thm_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
-- name    : Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b4932dc3-2aa0-5bb4-97aa-878c3c3d30b6
-- title:
--   Matching ℚ- and ℤₚ-bases across a base-change isomorphism
-- statement:
--   Let $p$ be a prime, let $A$ be a finite-dimensional $\mathbb{Q}$-vector space (an additive commutative group with a $\mathbb{Q}$-module structure that is module-finite over $\mathbb{Q}$), and let $H_p$ be an additive commutative group with a $\mathbb{Z}_p$-module structure that is module-finite and flat over $\mathbb{Z}_p$. Suppose given a $\mathbb{Q}_p$-linear isomorphism $\varphi \colon \mathbb{Q}_p \otimes_{\mathbb{Q}} A \xrightarrow{\ \sim\ } \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H_p$, where the first tensor product is taken along $\mathbb{Q} \to \mathbb{Q}_p$ and the second along $\mathbb{Z}_p \to \mathbb{Q}_p$. The conclusion asserts the existence of a natural number $n$, a basis $b$ of $A$ over $\mathbb{Q}$ indexed by $\mathrm{Fin}\,n$, and a basis $b_{H_p}$ of $H_p$ over $\mathbb{Z}_p$ indexed by the same $\mathrm{Fin}\,n$, such that for every index $i$ one has $\varphi(1 \otimes b_i) = 1 \otimes (b_{H_p})_i$. Thus the two bases correspond to one another term by term under $\varphi$; in particular $A$ and $H_p$ have the same rank $n$.
--
--   This is the descent step for a $\mathbb{Z}_p$-lattice along the completion $\mathbb{Q} \hookrightarrow \mathbb{Q}_p$: a finite flat $\mathbb{Z}_p$-module identified with a lattice in $\mathbb{Q}_p \otimes_{\mathbb{Q}} A$ admits a $\mathbb{Z}_p$-basis lying in $A$. It is used in the construction of a finite flat Hopf order over $\mathbb{Z}_p$ attached to a rational Hopf algebra, namely by [`HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic`](thm.html#HopfAlgebra.exists_finiteFlat_hopfOrder_ratLocalizedAt_of_algEquiv_baseChange_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
    (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℚ A] [Module.Finite ℚ A]
    (Hp : Type*) [AddCommGroup Hp] [Module ℤ_[p] Hp]
    [Module.Finite ℤ_[p] Hp] [Module.Flat ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp)) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ A) (bHp : Basis (Fin n) ℤ_[p] Hp),
      ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i) := by sorry
