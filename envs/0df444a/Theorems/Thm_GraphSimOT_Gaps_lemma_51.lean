-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_51
-- name    : GraphSimOT.Gaps.lemma_51
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:41.687821+00:00
-- url     : https://prove2.me/theorems/9e153688-e760-4615-96ee-25656b0830b0
-- title:
--   Lemma 51 — local agreement for the spectral distance: n⁻² Σ Q_ij (x_i − (Qᵀx)_j)² ≤ γ_Q(A′, B′)² ‖y‖₂²
-- statement:
--   Let $Q\in\mathrm{DS}(n)$, $A', B'\in\mathbb R^{n\times n}$ and $y\in\mathbb R^n$, and let $x := A'y$. Then
--   $$\frac1{n^2}\sum_{i,j\in[n]}Q_{ij}\big(x_i - (Q^\top x)_j\big)^2\ \le\ \gamma_Q(A',B')^2\,\|y\|_2^2,$$
--   where $(Q^\top x)_j = \sum_iQ_{ij}x_i$ and $\gamma_Q(A',B')$ is the spectral discrepancy of Eq. (40).
--
--   This is the $\ell_2$ analogue of Lemma 37, used in the proof of Theorem 14 on spectral truncations of the centred adjacency matrix.
--
--   Differences from the source:
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
--   - encoding: ‖y‖₂² → ∑ i, y i ^ 2; reason: the definition of the Euclidean norm squared
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 48, Lemma 51

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Spectral

open Matrix

namespace GraphSimOT.Gaps

/-- Lemma 51 (Local Agreement, App. F.2, p. 48): for `Q ∈ DS(n)`, `A', B' ∈ ℝ^{n×n}`,
`y ∈ ℝ^n` and `x := A' y`, `n^{-2} ∑_{i,j} Q_ij (x_i − (Qᵀ x)_j)² ≤ γ_Q(A', B')² ‖y‖₂²`. -/
theorem lemma_51 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (A' B' : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    (1 / (n : ℝ) ^ 2) * ∑ i, ∑ j, Q i j * ((A' *ᵥ y) i - (Qᵀ *ᵥ (A' *ᵥ y)) j) ^ 2
      ≤ gammaQ Q A' B' ^ 2 * ∑ i, y i ^ 2 := by sorry

end GraphSimOT.Gaps
