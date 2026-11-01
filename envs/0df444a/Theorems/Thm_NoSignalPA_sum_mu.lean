-- Prove2me | Theorems.Thm_NoSignalPA_sum_mu
-- name    : NoSignalPA.sum_mu
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:04:51.66686+00:00
-- url     : https://prove2.me/theorems/089a0c27-335f-4ba8-baa7-bca80f65ef20
-- title:
--   $\sum_{\mathbf a}\mu_{\mathbf a}=4^{-N_r}$ and $\sum_{\mathbf a}\mu_{\mathbf a}^2\le2^{-5N_r}5^{2M}$ (corrected: $\Gamma_{\mathbf a}$ from transposed tables)
-- statement:
--   Fix an entry $(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$, let $\mu_{\mathbf a}=\Gamma_{\mathbf a}(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$ and $M=\|\mathbf a_0\oplus\mathbf b_0\oplus\mathbf x_0\cdot\mathbf y_0\|$. Then, summing over all $\mathbf a\in\{0,1\}^{N_r}$,
--
--   $$
--   \sum_{\mathbf a}\mu_{\mathbf a}=4^{-N_r}\qquad\text{and}\qquad\sum_{\mathbf a}\mu_{\mathbf a}^2\le 2^{-5N_r}\,5^{2M}.
--   $$
--
--   The first identity gives the mean of $\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}$ for a random hash function; the second controls its variance.
--
--   Differences from the source:
--   - correction: |Γ_a⟩ built from the tables |γ₀⟩, |γ₁⟩ printed in Lemma 1 (p. 2) → |Γ_a⟩ built from their transposes (gammaCoef); reason: the printed tables are transposed relative to layout (3): for Nr = 1 and the nonsignaling box a = 1 ⊕ x, b = 0, P_{a=0|x=0} = 0 but the printed ⟨γ₀|P⟩ = 1; with the transposes Lemma 1 holds; this statement is unchanged by the transposition, because a ⊕ b ⊕ x·y is symmetric under (a, x) ↔ (b, y)
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, p.5

import Mathlib
import Definitions.Def_NoSignalPA_gammaVec
import Definitions.Def_NoSignalPA_ones

namespace NoSignalPA

/-- **`Σ_a μ_a = 4^{−Nr}` and `Σ_a μ_a² ≤ 2^{−5Nr} 5^{2M}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, p. 5 (PDF p. 5): "With a little work one obtains
`Σ_a µ_a = 4^{−Nr}` and `Σ_a µ_a² ≤ 2^{−5Nr} 5^{2M}`."

For a fixed entry `(a₀, b₀, x₀, y₀)`, with `μ_s = Γ_s(a₀, b₀, x₀, y₀)` and
`M = ‖a₀ ⊕ b₀ ⊕ x₀·y₀‖`: the sum of `μ_s` over all strings `s` is `4^{−Nr}`, and the sum of
`μ_s²` is at most `2^{−5Nr} 5^{2M}`. -/
theorem sum_mu {Nr : ℕ} (a₀ b₀ x₀ y₀ : Str Nr) :
    ∑ s : Str Nr, gammaVec s a₀ b₀ x₀ y₀ = ((4 : ℝ) ^ Nr)⁻¹ ∧
      ∑ s : Str Nr, (gammaVec s a₀ b₀ x₀ y₀) ^ 2
        ≤ ((2 : ℝ) ^ (5 * Nr))⁻¹
            * 5 ^ (2 * ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i))) := by sorry

end NoSignalPA
