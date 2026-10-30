-- Prove2me | Theorems.Thm_KingDiagonal_eq_14
-- name    : KingDiagonal.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:43.696931+00:00
-- url     : https://prove2.me/theorems/91e999d1-4b54-49a3-9541-8934e0cc9dc5
-- title:
--   Eq. (14): $(I\otimes\Psi)\big((A\otimes J)*\tau\big) = (A\otimes J)*\big((I\otimes\Psi)(\tau)\big)$
-- statement:
--   Let $\Psi$ be a completely positive map from $k\times k$ to $m\times m$ matrices, $A$ an $n\times n$ matrix and $\tau$ a matrix on $\mathbb C^n\otimes\mathbb C^k$. Write $J_k$, $J_m$ for the all-ones matrices. Then the Hadamard decomposition commutes with the action of $\Psi$ on the second factor:
--
--   $$
--   (I\otimes\Psi)\big((A\otimes J_k) * \tau\big) = (A\otimes J_m) * \big((I\otimes\Psi)(\tau)\big).
--   $$
--
--   Applied to $\rho = (A\otimes J_k)*\tau$ from (12), this gives King's (14), $(I\otimes\Psi)(\rho) = (A\otimes J_k)*\big((I\otimes\Psi)(\tau)\big)$.
--
--   **Formalization Note** $I\otimes\Psi$ is the tensor product of the identity on $M_n$ with $\Psi$, defined on all matrices through matrix units, block index first.
--
--   Differences from the source:
--   - generalization: A and τ built from a state ρ by (10)–(11) → arbitrary A : Matrix n n ℂ and τ : Matrix (n × k) (n × k) ℂ; reason: the identity holds for every A and τ; the page's A, τ are an instance
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: Φ ⊗ Ψ and I ⊗ Ψ on n × n block matrices with k × k blocks → superopTensor Φ Ψ and superopTensor id Ψ on Matrix (n × k) (n × k) ℂ, block index first; reason: superopTensor is the matrix-unit extension, equal to Φ ⊗ Ψ for linear Φ, Ψ; same block layout as the page
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (14), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open scoped Matrix Kronecker

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (14), p.5: the decomposition `ρ = (A ⊗ J_k) ∗ τ` of (12)
commutes with the action of `Ψ` on the second factor:
`(I ⊗ Ψ)((A ⊗ J_k) ∗ τ) = (A ⊗ J) ∗ ((I ⊗ Ψ)(τ))`.

**Formalization Note.** `I ⊗ Ψ` is `superopTensor id Ψ` (the tensor product of maps, defined on
every matrix through matrix units, first factor `n`). `Ψ : M_k → M_m` is completely positive,
in finite Kraus form (`FiniteKrausCP`); its output dimension `m` may differ from `k`, so the
all-ones matrix on the right is `J_m`. The identity is stated for every `A` and every `τ`, not only
those built from a state by (10)–(11). -/
theorem eq_14 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (A : Matrix n n ℂ) (τ : Matrix (n × k) (n × k) ℂ) :
    superopTensor (id : Superop n n) Ψ ((A ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix k k ℂ)) ⊙ τ) =
      (A ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix m m ℂ)) ⊙
        superopTensor (id : Superop n n) Ψ τ := by sorry

end KingDiagonal
