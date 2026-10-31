-- Prove2me | Theorems.Thm_MaxEntSampling_lemma_2
-- name    : MaxEntSampling.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:39.082703+00:00
-- url     : https://prove2.me/theorems/2a2f55a7-f9e2-413b-80eb-2463fd8dcd67
-- title:
--   Lemma 2 (lemma 14, Nikolov 2015) — the index $k$ exists and is unique (corrected: $\lambda\in\mathbb R^d_+$)
-- statement:
--   Let $\lambda\in\mathbb R^d_+$ with $\lambda_1\ge\cdots\ge\lambda_d\ge0$ and let $s\in[d]$. There exists a unique integer $0\le k<s$ such that
--
--   $$
--   \lambda_k \;>\; \frac{1}{s-k}\sum_{i\in[k+1,d]}\lambda_i \;\ge\; \lambda_{k+1},
--   $$
--
--   with the convention $\lambda_0=\infty$.
--
--   The integer $k$ defines $\Gamma_s$ (Definition 2), the objective of the relaxation PC (9).
--
--   **Formalization Note** The condition is `IsKIndex s lam k` with 0-based indices.
--
--   Differences from the source:
--   - correction: λ ∈ R^d with λ1 ≥ ··· ≥ λd → λ antitone with λ_i ≥ 0 for all i; reason: the printed statement is false: d = 2, s = 1, λ = (−1, −2); the only candidate k = 0 needs (λ1 + λ2)/1 = −3 ≥ λ1 = −1. The paper applies the lemma only to eigenvalues of X ⪰ 0, which are nonnegative, as in Nikolov (2015)
--   - encoding: convention λ0 = ∞ → the condition on λ_k is vacuous for k = 0; reason: same instances; 0-based indices
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 2, p.8 (PDF p.8)

import Mathlib
import Definitions.Def_MaxEntSampling_IsKIndex

namespace MaxEntSampling

/-- **Lemma 2 (lemma 14 of Nikolov 2015): the index `k` exists and is unique (corrected: `λ ∈ ℝ^d_+`).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 2, p.8 (PDF p.8): "Given a vector λ ∈ R^d with its elements sorted by
λ1 ≥ ··· ≥ λd and an integer s ∈ [d], there exists a unique integer 0 ≤ k < s such that
λk > (1/(s−k)) Σ_{i∈[k+1,d]} λi ≥ λk+1, where by convention λ0 = ∞."

For every `λ₁ ≥ ⋯ ≥ λ_d ≥ 0` and every `s ∈ [d]` there is exactly one integer `k` with
`0 ≤ k < s` and `λ_k > (1/(s−k)) Σ_{i∈[k+1,d]} λ_i ≥ λ_{k+1}` (`λ₀ = ∞`).

**Formalization Note.** The vector is `lam : Fin d → ℝ` with 0-based indices; the condition is
`IsKIndex s lam k`. The nonnegativity `λ_d ≥ 0` corrects the printed statement, which is false
for general `λ ∈ ℝ^d`: at `d = 2`, `s = 1`, `λ = (−1, −2)` the only candidate `k = 0` needs
`(λ₁ + λ₂)/1 = −3 ≥ λ₁ = −1`. The paper applies the lemma only to eigenvalues of positive
semidefinite matrices (Definition 2), which are nonnegative, as in Nikolov (2015). -/
theorem lemma_2 {d : ℕ} (s : ℕ) (hs1 : 1 ≤ s) (hsd : s ≤ d) (lam : Fin d → ℝ)
    (hanti : Antitone lam) (hnn : ∀ i, 0 ≤ lam i) :
    ∃! k : ℕ, IsKIndex s lam k := by sorry

end MaxEntSampling
