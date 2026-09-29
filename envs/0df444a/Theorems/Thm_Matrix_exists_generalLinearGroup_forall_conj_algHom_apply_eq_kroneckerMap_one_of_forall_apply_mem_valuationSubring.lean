-- Prove2me | Theorems.Thm_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring
-- name    : Matrix.exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/e1187c87-417f-5217-91ee-2a643cd6c064
-- title:
--   Integral M₂-representations over a valuation ring are standard
-- statement:
--   Let $K$ be a field, $\mathcal{O} \subseteq K$ a valuation subring, and $n$ a nonempty finite type with decidable equality. Let $\rho : M_2(K) \to M_{2\times n}(K)$ be a homomorphism of $K$-algebras, where the target is the algebra of matrices indexed by `Fin 2 × n`, and assume $\rho$ is entrywise integral in the sense that for every $m \in M_2(K)$ all of whose entries lie in $\mathcal{O}$, all entries of $\rho(m)$ lie in $\mathcal{O}$. The conclusion asserts the existence of an invertible matrix $P \in \mathrm{GL}_{2\times n}(K)$ such that every entry of $P$ lies in $\mathcal{O}$, every entry of $P^{-1}$ lies in $\mathcal{O}$, and for every $m \in M_2(K)$ one has $P \cdot \rho(m) \cdot P^{-1} = m \otimes 1_n$, the Kronecker product `Matrix.kroneckerMap (· * ·)` of $m$ with the identity matrix of size $n$, whose $((i,s),(j,t))$ entry is $m_{ij}\delta_{st}$. Thus an integral $K$-algebra map from $M_2(K)$ into a matrix algebra of size $2|n|$ becomes the standard diagonal embedding after conjugation by a change of basis that is integral in both directions.
--
--   This is the statement that all representations of the matrix algebra $M_2$ are equivalent to multiples of the standard one, in the refined form needed over a valuation ring: the conjugating matrix may be chosen together with its inverse integral, so that it also identifies the lattice $\mathcal{O}^{2|n|}$ with a standard one. It is used in the local analysis of quaternionic orders, being cited in the treatment of local conditions for units of a maximal order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Kronecker

theorem Matrix.exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring
    (K : Type) [Field K] (𝒪 : ValuationSubring K) (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2 × n) (Fin 2 × n) K)
    (hρ : ∀ m : Matrix (Fin 2) (Fin 2) K, (∀ i j, m i j ∈ 𝒪) → ∀ i j, ρ m i j ∈ 𝒪) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2 × n) K,
      (∀ i j, (P : Matrix (Fin 2 × n) (Fin 2 × n) K) i j ∈ 𝒪) ∧
      (∀ i j, ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2 × n) K) : Matrix (Fin 2 × n) (Fin 2 × n) K) i j ∈ 𝒪) ∧
      ∀ m : Matrix (Fin 2) (Fin 2) K,
        (P : Matrix (Fin 2 × n) (Fin 2 × n) K) * ρ m *
            ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2 × n) K) : Matrix (Fin 2 × n) (Fin 2 × n) K) =
          Matrix.kroneckerMap (· * ·) m (1 : Matrix n n K) := by sorry
