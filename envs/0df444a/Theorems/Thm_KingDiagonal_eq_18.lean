-- Prove2me | Theorems.Thm_KingDiagonal_eq_18
-- name    : KingDiagonal.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:40.644478+00:00
-- url     : https://prove2.me/theorems/bf1c8361-137a-4281-8129-5396bc51d220
-- title:
--   Eqs. (16)–(18): $\Psi((\tau)_{ii}) = V_iV_i^*$ and $\|V_iV_i^*\|_p \le \nu_p(\Psi)$
-- statement:
--   Let $\Psi$ be a completely positive map from $k\times k$ to $m\times m$ matrices, $\rho$ a state on $\mathbb C^n\otimes\mathbb C^k$, $\tau$ as in (11), and let $V_1,\dots,V_n$ be the block rows of $\big((I\otimes\Psi)(\tau)\big)^{1/2}$ as in (16). Then for every index $i$ and every real $p\ge1$:
--
--   1. the $i$-th diagonal block of $(I\otimes\Psi)(\tau)$ is $\Psi((\tau)_{ii}) = V_iV_i^*$;
--   2. $$\|V_iV_i^*\|_p \le \nu_p(\Psi),$$ where $\|\cdot\|_p$ is the Schatten $p$-norm and $\nu_p(\Psi) = \sup_\sigma \|\Psi(\sigma)\|_p$ over states $\sigma$ on $\mathbb C^k$.
--
--   The bound holds because $(\tau)_{ii}$ is a state; it is what controls each block of the factorization in Section 4.
--
--   **Formalization Note** $(\tau)_{ii}$ is the $k\times k$ block $a,b \mapsto \tau_{(i,a),(i,b)}$; the square root is the functional-calculus square root.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - generalization: (11) divides by (α_iα_j)^{1/2}, tacitly assuming every α_i > 0 → every state, with (√(α_iα_j))⁻¹ read as 0 when α_iα_j = 0; reason: for states with all α_i > 0 the Lean τ is the page's τ; the remaining states are extra instances on which the claim is still true
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: real matrix powers X^p, X^{p/2}, X^{1/2} of positive semidefinite matrices → cfc (fun x : ℝ => x ^ p) X, cfc Real.sqrt X; reason: the continuous functional calculus gives the usual powers on PSD (Hermitian, nonnegative spectrum) matrices, the only inputs used
--   - encoding: ν_p(Φ) = sup_ρ ‖Φ(ρ)‖_p over states, ‖X‖_p = (Tr X^p)^{1/p} on PSD outputs, p real ≥ 1 → nu (ENNReal.ofReal p) Φ: real sSup over density matrices of schattenNorm = (Re Tr (XᴴX)^{p/2})^{1/p}; reason: for p ≥ 1 and the PSD outputs of a CP map this is the page's p-norm and supremum (the set is nonempty and bounded whenever the input type is nonempty)
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eqs. (16)–(18), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_tau
import Definitions.Def_KingDiagonal_sqrtBlockRow

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)
open scoped Matrix

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eqs. (16)–(18), p.5: for a CP map `Ψ` and a state `ρ` on
`C^{kn}`, with `τ` as in (11) and `V_1, …, V_n` the block rows of `((I ⊗ Ψ)(τ))^{1/2}` (16), the
diagonal blocks of `(I ⊗ Ψ)(τ) = (V_i V_j*)_{ij}` (17) are `Ψ((τ)_{ii}) = V_i V_i*`, and for every
`p ≥ 1`, `‖V_i V_i*‖_p ≤ ν_p(Ψ)` (18).

**Formalization Note.** `(τ)_{ii}` is `fun a b => tau ρ (i, a) (i, b)`; `‖·‖_p` is `schattenNorm` at
`ENNReal.ofReal p`, and `ν_p` is `nu` (supremum over density matrices). `Ψ : M_k → M_m` is in
finite Kraus form with output dimension `m` arbitrary. Both clauses are asserted for every `i`,
including `α_i = 0` (then `(τ)_{ii} = 0` under `0⁻¹ = 0`). -/
theorem eq_18 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) (i : n) (p : ℝ) (hp : 1 ≤ p) :
    sqrtBlockRow (superopTensor (id : Superop n n) Ψ (tau ρ)) i *
          (sqrtBlockRow (superopTensor (id : Superop n n) Ψ (tau ρ)) i)ᴴ =
        Ψ (Matrix.of fun a b => tau ρ (i, a) (i, b)) ∧
      schattenNorm (ENNReal.ofReal p)
          (sqrtBlockRow (superopTensor (id : Superop n n) Ψ (tau ρ)) i *
            (sqrtBlockRow (superopTensor (id : Superop n n) Ψ (tau ρ)) i)ᴴ) ≤
        nu (ENNReal.ofReal p) Ψ := by sorry

end KingDiagonal
