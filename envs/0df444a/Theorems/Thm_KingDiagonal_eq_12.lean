-- Prove2me | Theorems.Thm_KingDiagonal_eq_12
-- name    : KingDiagonal.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:24.856495+00:00
-- url     : https://prove2.me/theorems/4392e6da-2729-487b-a50c-456125b65467
-- title:
--   Eq. (12): $\rho = (A\otimes J_k) * \tau$
-- statement:
--   Let $\rho$ be a state on $\mathbb C^{n}\otimes\mathbb C^{k}$ (positive semidefinite with trace $1$), viewed as an $n\times n$ block matrix with $k\times k$ blocks. Let $\alpha_i = \operatorname{Tr}(\rho)_{ii}$, let $\tau$ have blocks $(\tau)_{ij} = (\alpha_i\alpha_j)^{-1/2}(\rho)_{ij}$, and let $A_{ij} = (\alpha_i\alpha_j)^{1/2}$. With $J_k$ the $k\times k$ matrix with all entries equal to $1$ and $*$ the Hadamard product,
--
--   $$
--   \rho = (A\otimes J_k) * \tau .
--   $$
--
--   This rewrites the input state as a Hadamard product in which the first tensor factor carries only the $n\times n$ matrix $A$, on which a diagonal map acts.
--
--   **Formalization Note** $A\otimes J_k$ is the Kronecker product with block index first.
--
--   Differences from the source:
--   - generalization: ρ a state on C^{kn} for some k ≥ 1 → any finite index type k, possibly empty; reason: for k empty both sides are the empty matrix; for nonempty k it is the page's statement
--   - generalization: (11) divides by (α_iα_j)^{1/2}, tacitly assuming every α_i > 0 → every state, with (√(α_iα_j))⁻¹ read as 0 when α_iα_j = 0; reason: for states with all α_i > 0 the Lean τ is the page's τ; the remaining states are extra instances on which the claim is still true
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (12), p.4 (with (10), (11), (13))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_KingDiagonal_weightMatrix
import Definitions.Def_KingDiagonal_tau

open QAlgorithms
open scoped Matrix Kronecker

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (12), p.4: let `ρ` be a state on `C^{kn}` (positive
semidefinite, trace 1), written as an `n × n` block matrix with `k × k` blocks; with
`α_i = Tr (ρ)_{ii}` (10), `(τ)_{ij} = (α_i α_j)^{-1/2} (ρ)_{ij}` (11) and `A_{ij} = (α_i α_j)^{1/2}`,
`ρ = (A ⊗ J_k) ∗ τ`, where `J_k` is the all-ones `k × k` matrix (13) and `∗` is the Hadamard
product (5).

**Formalization Note.** Block index first: `Matrix (n × k) (n × k) ℂ`, and `A ⊗ J_k` is the
Kronecker product `A ⊗ₖ J_k`. Under Lean's `0⁻¹ = 0` (see `tau`), the identity is asserted for every
state, including states with some `α_i = 0`, where (11) is undefined on the page. -/
theorem eq_12 {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) :
    ρ = (weightMatrix ρ ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix k k ℂ)) ⊙ tau ρ := by sorry

end KingDiagonal
