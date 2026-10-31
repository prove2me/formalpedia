-- Prove2me | Theorems.Thm_NetServicePricing_fact_8
-- name    : NetServicePricing.fact_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:11.626928+00:00
-- url     : https://prove2.me/theorems/aa8cc751-d096-440c-a6ef-8c6fe3e9087e
-- title:
--   Fact 8 — Blakley–Roy: $\langle A^k\mathbf 1,\mathbf 1\rangle\ge n^{1-k}\langle A\mathbf 1,\mathbf 1\rangle^k$
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix with nonnegative entries. For every nonnegative integer $k$,
--
--   $$\langle A^k\mathbf 1,\mathbf 1\rangle\ \ge\ n^{1-k}\,\langle A\mathbf 1,\mathbf 1\rangle^k .$$
--
--   For an adjacency matrix, $\langle A^k\mathbf 1,\mathbf 1\rangle$ is the (weighted) number of walks of length $k$ and $\langle A\mathbf 1,\mathbf 1\rangle/n$ is the average degree, so the inequality says that a graph has at least as many walks of each length as the regular graph of the same average degree. This is Theorem 1 of Blakley and Roy (1965).
--
--   **Formalization Note** $\langle y,\mathbf 1\rangle$ is the dot product with the all-ones vector.
--
--   Differences from the source:
--   - encoding: n^{1−k} → the integer power (n : ℝ) ^ ((1 : ℤ) − k); reason: same value for n ≥ 1; at n = 0, where the paper's power is undefined, Lean's 0 ^ m = 0 (m ≠ 0) makes both sides 0
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Fact 8, p.ec2 (Theorem 1 in Blakley and Roy (1965))

import Mathlib

open Matrix

namespace NetServicePricing

/-- **Fact 8 (Blakley–Roy inequality).**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Fact 8 (Theorem 1 in Blakley and Roy (1965)), p.ec2: "For a nonnegative and symmetric
matrix A and any nonnegative integer k, we have ⟨A^k1,1⟩ ≥ n^{1−k}⟨A1,1⟩^k."

For every real symmetric entrywise nonnegative `n × n` matrix `A` and every `k ∈ ℕ`,
`n^{1−k} ⟨A𝟏, 𝟏⟩^k ≤ ⟨A^k 𝟏, 𝟏⟩`.

**Formalization Note** `n^{1−k}` is the integer power `(n : ℝ) ^ ((1 : ℤ) - k)`; at `n = 0`
Lean's `0 ^ m = 0` for `m ≠ 0` makes both sides `0`, a case the paper does not consider.
`⟨y, 𝟏⟩` is `y ⬝ᵥ 1`. -/
theorem fact_8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsymm : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℤ) - k) * ((A *ᵥ (1 : Fin n → ℝ)) ⬝ᵥ (1 : Fin n → ℝ)) ^ k ≤
      (A ^ k *ᵥ (1 : Fin n → ℝ)) ⬝ᵥ (1 : Fin n → ℝ) := by sorry

end NetServicePricing
