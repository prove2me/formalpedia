-- Prove2me | Theorems.Thm_KingDiagonal_eq_15
-- name    : KingDiagonal.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:04.377631+00:00
-- url     : https://prove2.me/theorems/ae88894c-59c4-4080-b256-e0d7f3a6d4b3
-- title:
--   Eq. (15): $(\Phi\otimes\Psi)(\rho) = (\Phi(A)\otimes J)*\big((I\otimes\Psi)(\tau)\big)$
-- statement:
--   Let $\Phi$ be a diagonal map on $n\times n$ matrices ($\Phi(X) = C*X$ with $C\succeq0$), $\Psi$ a completely positive map from $k\times k$ to $m\times m$ matrices, and $\rho$ a state on $\mathbb C^n\otimes\mathbb C^k$. With $A$ and $\tau$ built from $\rho$ as in (10)–(12) and $J_m$ the $m\times m$ all-ones matrix,
--
--   $$
--   (\Phi\otimes\Psi)(\rho) = \big(\Phi(A)\otimes J_m\big) * \big((I\otimes\Psi)(\tau)\big).
--   $$
--
--   The diagonal map acts only on the $n\times n$ weight matrix $A$; the partner $\Psi$ acts only on $\tau$.
--
--   **Formalization Note** $\Phi\otimes\Psi$ and $I\otimes\Psi$ are the matrix-unit tensor products of maps, block index first.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - generalization: (11) divides by (α_iα_j)^{1/2}, tacitly assuming every α_i > 0 → every state, with (√(α_iα_j))⁻¹ read as 0 when α_iα_j = 0; reason: for states with all α_i > 0 the Lean τ is the page's τ; the remaining states are extra instances on which the claim is still true
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: Φ ⊗ Ψ and I ⊗ Ψ on n × n block matrices with k × k blocks → superopTensor Φ Ψ and superopTensor id Ψ on Matrix (n × k) (n × k) ℂ, block index first; reason: superopTensor is the matrix-unit extension, equal to Φ ⊗ Ψ for linear Φ, Ψ; same block layout as the page
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (15), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_IsDiagonalMap
import Definitions.Def_KingDiagonal_weightMatrix
import Definitions.Def_KingDiagonal_tau

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open scoped Matrix Kronecker

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (15), p.5: for a diagonal map `Φ` (Definition 3), a CP map
`Ψ` and a state `ρ` on `C^{kn}`, with `A` and `τ` as in (10)–(12),
`(Φ ⊗ Ψ)(ρ) = (Φ(A) ⊗ J) ∗ ((I ⊗ Ψ)(τ))`.

**Formalization Note.** `Φ ⊗ Ψ` is `superopTensor Φ Ψ` and `I ⊗ Ψ` is `superopTensor id Ψ`
(block index first). `Ψ : M_k → M_m` is in finite Kraus form, with output dimension `m` possibly
different from `k`, so the all-ones matrix is `J_m` (the page's `J_k` with `m = k`). States with
some `α_i = 0` are included (`0⁻¹ = 0` in `tau`). -/
theorem eq_15 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Φ : Superop n n) (hΦ : IsDiagonalMap Φ)
    (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) :
    superopTensor Φ Ψ ρ =
      (Φ (weightMatrix ρ) ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix m m ℂ)) ⊙
        superopTensor (id : Superop n n) Ψ (tau ρ) := by sorry

end KingDiagonal
