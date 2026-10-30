-- Prove2me | Theorems.Thm_KingDiagonal_eq_22
-- name    : KingDiagonal.eq_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:06.644603+00:00
-- url     : https://prove2.me/theorems/cd838e32-6579-406d-905d-c8129fe02581
-- title:
--   Eqs. (19)–(24): the factorization $(\Phi\otimes\Psi)(\rho) = VKV^*$
-- statement:
--   Let $\Phi$ be a diagonal map on $n\times n$ matrices, $\Psi$ a completely positive map from $k\times k$ to $m\times m$ matrices, and $\rho$ a state on $\mathbb C^n\otimes\mathbb C^k$, with $A$, $\tau$ as in (10)–(12) and $V_1,\dots,V_n$ the block rows of $\big((I\otimes\Psi)(\tau)\big)^{1/2}$ (16). Let
--
--   $$
--   V = \operatorname{diag}(V_1, V_2, \dots, V_n), \qquad K = \Phi(A)\otimes I',
--   $$
--
--   where $I'$ is the $nm\times nm$ identity matrix, so $V$ is $nm\times n^2m$. Then
--
--   $$
--   (\Phi\otimes\Psi)(\rho) = V\,K\,V^* .
--   $$
--
--   This puts the output of the product map in the form to which the Lieb–Thirring inequality (9) applies.
--
--   **Formalization Note** Block index first throughout; $V$ is `blockDiag` of the block rows and $K$ is a Kronecker product.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - generalization: (11) divides by (α_iα_j)^{1/2}, tacitly assuming every α_i > 0 → every state, with (√(α_iα_j))⁻¹ read as 0 when α_iα_j = 0; reason: for states with all α_i > 0 the Lean τ is the page's τ; the remaining states are extra instances on which the claim is still true
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: real matrix powers X^p, X^{p/2}, X^{1/2} of positive semidefinite matrices → cfc (fun x : ℝ => x ^ p) X, cfc Real.sqrt X; reason: the continuous functional calculus gives the usual powers on PSD (Hermitian, nonnegative spectrum) matrices, the only inputs used
--   - encoding: Φ ⊗ Ψ and I ⊗ Ψ on n × n block matrices with k × k blocks → superopTensor Φ Ψ and superopTensor id Ψ on Matrix (n × k) (n × k) ℂ, block index first; reason: superopTensor is the matrix-unit extension, equal to Φ ⊗ Ψ for linear Φ, Ψ; same block layout as the page
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eqs. (19)–(24), pp.5–6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_IsDiagonalMap
import Definitions.Def_KingDiagonal_weightMatrix
import Definitions.Def_KingDiagonal_tau
import Definitions.Def_KingDiagonal_sqrtBlockRow
import Definitions.Def_KingDiagonal_blockDiag

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open scoped Matrix Kronecker

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eqs. (19)–(24), pp.5–6: for a diagonal map `Φ`, a CP map `Ψ` and
a state `ρ` on `C^{kn}`, the output of the product map is written in the factorized form
`(Φ ⊗ Ψ)(ρ) = V K V*` (22), where `V = diag(V_1, V_2, …, V_n)` (23) is block diagonal with the block
rows `V_i` of `((I ⊗ Ψ)(τ))^{1/2}` (16) on its diagonal, and `K = Φ(A) ⊗ I′` (24), with `I′` the
identity matrix (p.6) and `A`, `τ` as in (10)–(12).

**Formalization Note.** `Φ ⊗ Ψ` is `superopTensor Φ Ψ`, `I ⊗ Ψ` is `superopTensor id Ψ`, block index
first. `Ψ : M_k → M_m` is in finite Kraus form with output dimension `m` arbitrary (the page has
`m = k`), so `V_i` is `m × nm`, `V` is `nm × n²m`, and `I′` is the `nm × nm` identity. States with some
`α_i = 0` are included (`0⁻¹ = 0` in `tau`). -/
theorem eq_22 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Φ : Superop n n) (hΦ : IsDiagonalMap Φ)
    (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) :
    let V : Matrix (n × m) (n × (n × m)) ℂ :=
      blockDiag (sqrtBlockRow (superopTensor (id : Superop n n) Ψ (tau ρ)))
    let K : Matrix (n × (n × m)) (n × (n × m)) ℂ :=
      Φ (weightMatrix ρ) ⊗ₖ (1 : Matrix (n × m) (n × m) ℂ)
    superopTensor Φ Ψ ρ = V * K * Vᴴ := by sorry

end KingDiagonal
