-- Prove2me | Theorems.Thm_NoSignalPA_abs_mu_le
-- name    : NoSignalPA.abs_mu_le
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:04:51.763758+00:00
-- url     : https://prove2.me/theorems/b472fff9-4898-4663-bbc6-ff972ad097b7
-- title:
--   $|\mu_{\mathbf a}|\le 5^M8^{-N_r}$ (corrected: $\Gamma_{\mathbf a}$ from transposed tables)
-- statement:
--   Fix an entry $(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$ and let $M=\|\mathbf a_0\oplus\mathbf b_0\oplus\mathbf x_0\cdot\mathbf y_0\|$. For every string $\mathbf a$, the coefficient $\mu_{\mathbf a}=\Gamma_{\mathbf a}(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$ satisfies
--
--   $$
--   |\mu_{\mathbf a}|\le 5^M\,8^{-N_r}.
--   $$
--
--   This is the uniform bound on the weights that makes the exponential-moment argument of Lemma 2 applicable.
--
--   Differences from the source:
--   - correction: |Γ_a⟩ built from the tables |γ₀⟩, |γ₁⟩ printed in Lemma 1 (p. 2) → |Γ_a⟩ built from their transposes (gammaCoef); reason: the printed tables are transposed relative to layout (3): for Nr = 1 and the nonsignaling box a = 1 ⊕ x, b = 0, P_{a=0|x=0} = 0 but the printed ⟨γ₀|P⟩ = 1; with the transposes Lemma 1 holds; this statement is unchanged by the transposition, because a ⊕ b ⊕ x·y is symmetric under (a, x) ↔ (b, y)
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, p.5

import Mathlib
import Definitions.Def_NoSignalPA_gammaVec
import Definitions.Def_NoSignalPA_ones

namespace NoSignalPA

/-- **`|μ_a| ≤ 5^M 8^{−Nr}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, p. 5 (PDF p. 5): "Let `µ_a = Γ_a(a0, b0, x0, y0)`,
`M = ‖a0 ⊕ b0 ⊕ x0 · y0‖`, and note that `|µ_a| ≤ 5^M 8^{−Nr}` for all a."

For a fixed entry `(a₀, b₀, x₀, y₀)` and every string `s` (the paper's `a`),
`|Γ_s(a₀, b₀, x₀, y₀)| ≤ 5^M · 8^{−Nr}` with `M = ‖a₀ ⊕ b₀ ⊕ x₀·y₀‖`.

**Formalization Note.** `Γ_s` is the corrected vector (transposed tables); the bound holds for
the printed tables too, since `a ⊕ b ⊕ x·y` is symmetric under `(a, x) ↔ (b, y)`. -/
theorem abs_mu_le {Nr : ℕ} (s a₀ b₀ x₀ y₀ : Str Nr) :
    |gammaVec s a₀ b₀ x₀ y₀|
      ≤ 5 ^ ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i)) * ((8 : ℝ) ^ Nr)⁻¹ := by sorry

end NoSignalPA
