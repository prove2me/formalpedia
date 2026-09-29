-- Prove2me | Theorems.Thm_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
-- name    : Matrix.exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/2cec89c6-bb76-5545-9b0b-371a479e8afd
-- title:
--   Transferring lattice-saturation between two embeddings into Mₙ(ℚₚ)
-- statement:
--   Let $p$ be a prime, $A$ a ring, and $n$ a finite index set with decidable equality. Let $\theta, E \colon A \to M_n(\mathbb{Q}_p)$ be two injective ring homomorphisms, and let $m$ be a natural number. Assume first that $\theta$ hits every matrix of the form $p^m M$ with $M \in M_n(\mathbb{Z}_p)$: for each $M : \mathrm{Matrix}\ n\ n\ \mathbb{Z}_p$ there is $a \in A$ with $\theta(a) = p^m \cdot (M$ viewed in $M_n(\mathbb{Q}_p)$ via the inclusion $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p)$, the scalar $p^m$ being taken in $\mathbb{Q}_p$. Assume second that $E$ is integral, i.e. for every $a \in A$ there is $M : \mathrm{Matrix}\ n\ n\ \mathbb{Z}_p$ with $E(a)$ equal to the image of $M$ in $M_n(\mathbb{Q}_p)$. The conclusion is that some natural number $m'$ has the corresponding property for $E$: for every $M : \mathrm{Matrix}\ n\ n\ \mathbb{Z}_p$ there is $a \in A$ with $E(a) = p^{m'} \cdot (M$ viewed in $M_n(\mathbb{Q}_p))$. Thus the image of $E$ contains $p^{m'} M_n(\mathbb{Z}_p)$.
--
--   An elementary transfer statement: the property of having image containing a scaled copy of the standard lattice order $M_n(\mathbb{Z}_p)$ passes from one injective representation of $A$ on $\mathbb{Q}_p^n$ to any integral one, so that the image of $E$ spans $M_n(\mathbb{Q}_p)$ over $\mathbb{Q}_p$ and is an order when $n$ is non-empty. It is used in the Čerednik–Drinfeld part of the development, to pass from an abstract identification of an endomorphism algebra with $M_2(\mathbb{Q}_p)$ to the explicit homomorphism given by the action on a rank-two $\mathbb{Z}_p$-module, without appealing to Skolem–Noether.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Matrix.exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
    (p : ℕ) [Fact p.Prime] {A : Type u} [Ring A] {n : Type} [Fintype n] [DecidableEq n]
    (θ E : A →+* Matrix n n ℚ_[p]) (hθ : Function.Injective θ) (hE : Function.Injective E) (m : ℕ)
    (hθm : ∀ M : Matrix n n ℤ_[p], ∃ a : A, θ a = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEint : ∀ a : A, ∃ M : Matrix n n ℤ_[p], E a = M.map ((↑) : ℤ_[p] → ℚ_[p])) :
    ∃ m' : ℕ, ∀ M : Matrix n n ℤ_[p], ∃ a : A, E a = (p : ℚ_[p]) ^ m' • M.map ((↑) : ℤ_[p] → ℚ_[p]) := by sorry
