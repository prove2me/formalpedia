-- Prove2me | Theorems.Thm_LindbladStructLearn_corollary_4_6
-- name    : LindbladStructLearn.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:53:16.510987+00:00
-- url     : https://prove2.me/theorems/528d36d7-a59b-4c6a-af06-1ed28425b6a1
-- title:
--   Corollary 4.6 — $\|\mathcal L_\lambda^{\dagger\ell}(P)\|_{\mathrm{op}} \le \ell!(2ekg)^\ell$
-- statement:
--   Let $k \ge 1$, $g > 0$, and let $\lambda$ be a $k$-local coefficient vector with $\|\mathcal L_\lambda\|_{B_1} \le g$. Let $P$ be an $n$-qubit Pauli with $|\mathrm{supp}(P)| \le k$ and let $\ell \ge 2$. Then the spectral norm of the $\ell$-fold adjoint applied to $P$ satisfies
--
--   $$\big\|\mathcal L_\lambda^{\dagger\ell}(P)\big\|_{\mathrm{op}} \le \ell!\,(2ekg)^\ell.$$
--
--   The bound controls the Taylor coefficients of $e^{\mathcal L t}$ and shows that the series converges for $t$ of order $1/(kg)$.
--
--   Differences from the source:
--   - reading: P ∈ 𝒫_k (not defined in print) → an n-qubit Pauli P with |supp P| ≤ k; reason: its use in (5.83) is on P2RP1, supported in S_P̄ with s_P̄ ≤ k
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Corollary 4.6, Eq. (4.34), p.27

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_lindbladAdj
import Definitions.Def_LindbladStructLearn_IsKLocal
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Corollary 4.6 (operator norm bound; Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Eq. (4.34), p.27): for `P ∈ 𝒫_k`, `ℓ ≥ 2` and a
`k`-local superoperator `L_λ` with `‖L_λ‖_B1 ≤ g`, `‖L_λ^(†ℓ)(P)‖_op ≤ ℓ!(2ekg)^ℓ`.

**Formalization Note** `𝒫_k` (not defined in print) is read as the `n`-qubit Paulis with
`|supp P| ≤ k` (its use in Eq. (5.83) is on `P₂RP₁`, supported in `S_P̄`). `λ` is any `k`-local
coefficient vector. `‖·‖_op` is the spectral norm, the operator norm of the matrix on Euclidean
space (`Matrix.toEuclideanCLM`). `k, g > 0` is the paper's standing assumption (p.13). -/
theorem corollary_4_6 {n : ℕ} (k : ℕ) (hk : 0 < k) (g : ℝ) (hg : 0 < g)
    (lam : Pauli n × Pauli n → ℂ) (hloc : IsKLocal k lam) (hB1 : b1Norm lam ≤ g)
    (P : Pauli n) (hP : weight P ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Qubits n)
        (applySuper (lindbladAdj lam ^ ℓ) (pauliMatrix P))‖ ≤
      (ℓ.factorial : ℝ) * (2 * Real.exp 1 * k * g) ^ ℓ := by sorry

end LindbladStructLearn
