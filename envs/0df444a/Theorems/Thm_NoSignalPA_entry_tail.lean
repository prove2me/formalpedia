-- Prove2me | Theorems.Thm_NoSignalPA_entry_tail
-- name    : NoSignalPA.entry_tail
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:04:54.384449+00:00
-- url     : https://prove2.me/theorems/03b19c43-2c00-4b3a-ac5a-3f32bc69c103
-- title:
--   One-entry tail bound, both sides (corrected: $N_s+\sqrt{N_r}\le N_r+2$)
-- statement:
--   Assume $N_s+\sqrt{N_r}\le N_r+2$. Fix a key value $\mathbf k$ and an entry $(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$; let $\mu_{\mathbf a}=\Gamma_{\mathbf a}(\mathbf a_0,\mathbf b_0,\mathbf x_0,\mathbf y_0)$, $M=\|\mathbf a_0\oplus\mathbf b_0\oplus\mathbf x_0\cdot\mathbf y_0\|$ and
--
--   $$
--   T=2^{(\sqrt{N_r}-N_r-N_s)/2}\,4^{-N_r}\,5^{M}.
--   $$
--
--   For a uniformly random $h$ and $V_{\mathbf a}=[h(\mathbf a)=\mathbf k]$,
--
--   $$
--   \Pr\Bigl\{\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}\ge 2^{-N_s-2N_r}+T\Bigr\}\le e^{-2^{\sqrt{N_r}}/4}
--   \qquad\text{and}\qquad
--   \Pr\Bigl\{\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}\le 2^{-N_s-2N_r}-T\Bigr\}\le e^{-2^{\sqrt{N_r}}/4}.
--   $$
--
--   Since $2^{-N_s-2N_r}$ is the mean of $\sum_{\mathbf a}\mu_{\mathbf a}V_{\mathbf a}$, this says that one entry of $2^{N_s}|\Gamma_{\mathcal A_{\mathbf k}}\rangle$ deviates from $4^{-N_r}$ by more than the right side of (6) only with doubly exponentially small probability.
--
--   Differences from the source:
--   - correction: no hypothesis relating Ns and Nr ('the chosen value for β satisfies the required constraint') → hypothesis Ns + √Nr ≤ Nr + 2; reason: without it the bound is false: for Nr = 144, Ns = 160, k arbitrary and the entry a₀ = b₀ = x₀ = y₀ = 0, every μ_a = 8^{−144} and the event Σ μ_a V_a ≥ 2^{−448} + 2^{−434} is the event h^{−1}(k) ≠ ∅, of probability about 2^{−16} > e^{−1024}; the hypothesis is exactly the constraint |β 5^M 8^{−Nr}| ≤ 1 of (14) for β = 2^{(√Nr+Nr+Ns)/2−1} 4^{Nr} 5^{−M}, half the printed β (the printed β only gives the bound 1)
--   - correction: |Γ_a⟩ built from the tables |γ₀⟩, |γ₁⟩ printed in Lemma 1 (p. 2) → |Γ_a⟩ built from their transposes (gammaCoef); reason: the printed tables are transposed relative to layout (3): for Nr = 1 and the nonsignaling box a = 1 ⊕ x, b = 0, P_{a=0|x=0} = 0 but the printed ⟨γ₀|P⟩ = 1; with the transposes Lemma 1 holds; this statement is unchanged by the transposition, because a ⊕ b ⊕ x·y is symmetric under (a, x) ↔ (b, y)
--   - reading: 'The expression obtained when replacing ≥ with ≤ above' → Prob{Σ_a μ_a V_a ≤ 2^{−Ns−2Nr} − T} ≤ e^{−2^{√Nr}/4}; reason: replacing only the relation gives a false statement (the event contains the mean); the lower tail at the same distance below the mean is the one (15) needs
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, p.5

import Mathlib
import Definitions.Def_NoSignalPA_gammaVec
import Definitions.Def_NoSignalPA_ones
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

namespace NoSignalPA

/-- **The one-entry tail bound, both sides (hypothesis `Ns + √Nr ≤ Nr + 2`).**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, p. 5 (PDF p. 5): "`Prob{Σ_a µ_a V_a ≥ 2^{−Ns−2Nr} +
2^{(√Nr−Nr−Ns)/2} 4^{−Nr} 5^M} ≤ e^{−2^{√Nr}/4}`. Note that the chosen value for β satisfies the
required constraint. The expression obtained when replacing '≥' with '≤' above, can be derived in a
similar way."

Assume `Ns + √Nr ≤ Nr + 2`. Fix a key `k` and an entry `(a₀, b₀, x₀, y₀)`; let
`μ_s = Γ_s(a₀, b₀, x₀, y₀)`, `M = ‖a₀ ⊕ b₀ ⊕ x₀·y₀‖`, `c = 2^{−Ns−2Nr}` and
`T = 2^{(√Nr−Nr−Ns)/2} 4^{−Nr} 5^M`. For a uniformly random `h` and `V_s = [h(s) = k]`,
`Prob{Σ_s μ_s V_s ≥ c + T} ≤ e^{−2^{√Nr}/4}` and `Prob{Σ_s μ_s V_s ≤ c − T} ≤ e^{−2^{√Nr}/4}`.

**Formalization Note.** (1) Correction: the hypothesis `Ns + √Nr ≤ Nr + 2` is not on the page. It is
the constraint `|β 5^M 8^{−Nr}| ≤ 1` of (14) for the `β` that yields this bound,
`β = 2^{(√Nr+Nr+Ns)/2 − 1} 4^{Nr} 5^{−M}` (half the printed value, with which the exponent is
`0`). For long keys the paper's claim "the chosen value for β satisfies the required constraint"
is false. (2) The "≤" tail is the second conjunct, with `+T` replaced by `−T`. -/
theorem entry_tail {Nr Ns : ℕ} (hN : (Ns : ℝ) + Real.sqrt Nr ≤ Nr + 2) (k : Str Ns)
    (a₀ b₀ x₀ y₀ : Str Nr) :
    let μ : Str Nr → ℝ := fun s => gammaVec s a₀ b₀ x₀ y₀
    let M : ℕ := ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i))
    let c : ℝ := (2 : ℝ) ^ (-(Ns : ℝ) - 2 * Nr)
    let T : ℝ := (2 : ℝ) ^ ((Real.sqrt Nr - Nr - Ns) / 2) * ((4 : ℝ) ^ Nr)⁻¹ * 5 ^ M
    OAI.ThorpCompatibility.uniformProbability (fun h : Str Nr → Str Ns =>
        c + T ≤ ∑ s, μ s * (if h s = k then 1 else 0))
        ≤ Real.exp (-((2 : ℝ) ^ Real.sqrt Nr) / 4) ∧
      OAI.ThorpCompatibility.uniformProbability (fun h : Str Nr → Str Ns =>
        ∑ s, μ s * (if h s = k then 1 else 0) ≤ c - T)
        ≤ Real.exp (-((2 : ℝ) ^ Real.sqrt Nr) / 4) := by sorry

end NoSignalPA
