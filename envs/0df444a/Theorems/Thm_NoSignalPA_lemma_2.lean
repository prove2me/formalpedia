-- Prove2me | Theorems.Thm_NoSignalPA_lemma_2
-- name    : NoSignalPA.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:06:35.421997+00:00
-- url     : https://prove2.me/theorems/5ad2c4ea-f816-40d2-9f72-d85e13db7b88
-- title:
--   Lemma 2 — almost all $h$ satisfy (6) (corrected: $N_s+\sqrt{N_r}\le N_r+2$; $\Gamma_{\mathbf a}$ from transposed tables)
-- statement:
--   Assume $N_s+\sqrt{N_r}\le N_r+2$. For $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$ and $\mathbf k\in\{0,1\}^{N_s}$ let $\mathcal A_{\mathbf k}=h^{-1}(\mathbf k)$ and $|\Gamma_{\mathcal A_{\mathbf k}}\rangle=\sum_{\mathbf a\in\mathcal A_{\mathbf k}}|\Gamma_{\mathbf a}\rangle$. If $h$ is chosen uniformly at random, then the probability that the entrywise inequality
--
--   $$
--   \Bigl|\,2^{N_s}|\Gamma_{\mathcal A_{\mathbf k}}\rangle-4^{-N_r}|1s\rangle\Bigr|\ \preceq\ \sqrt{2^{\,N_s+\sqrt{N_r}}}\ |\mathrm{CHSH}\rangle^{\otimes N_r}\qquad(6)
--   $$
--
--   fails for some $\mathbf k$ is less than
--
--   $$
--   2\exp\bigl(5N_r-2^{\sqrt{N_r}}/4\bigr).
--   $$
--
--   Here $|1s\rangle\in\mathbb R^{16^{N_r}}$ has all entries equal to one, $|\cdot|$ is the entrywise absolute value and $\preceq$ the entrywise order. Lemma 2 is the random-hashing half of the proof of the main result; the other half derives security from (6).
--
--   Differences from the source:
--   - correction: Lemma 2 for all Nr, Ns → hypothesis Ns + √Nr ≤ Nr + 2; reason: for Nr = 144, Ns = 160 (6) fails for every h at the entry a = b = x = y = 0 and any k in the image of h (left side ≥ 2^{−272}(1 − 2^{−16}), right side 2^{−274}), while the claimed failure probability 2exp(720 − 1024) is below 1; the added hypothesis is the constraint the proof needs
--   - correction: |Γ_a⟩ built from the tables |γ₀⟩, |γ₁⟩ printed in Lemma 1 (p. 2) → |Γ_a⟩ built from their transposes (gammaCoef); reason: the printed tables are transposed relative to layout (3): for Nr = 1 and the nonsignaling box a = 1 ⊕ x, b = 0, P_{a=0|x=0} = 0 but the printed ⟨γ₀|P⟩ = 1; with the transposes Lemma 1 holds; this statement is unchanged by the transposition, because a ⊕ b ⊕ x·y is symmetric under (a, x) ↔ (b, y)
--   - encoding: 'almost all functions h satisfy (6)' → OAI.ThorpCompatibility.uniformProbability (fun h => ¬ SatisfiesEq6 h) < 2 exp(5Nr − 2^{√Nr}/4); reason: the definition of 'almost all' on p.2
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Lemma 2, eq. (6), p.2; proof in the Appendix, eq. (15), p.5

import Mathlib
import Definitions.Def_NoSignalPA_SatisfiesEq6
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

namespace NoSignalPA

/-- **Lemma 2 (corrected: `Ns + √Nr ≤ Nr + 2`): almost all `h` satisfy (6).**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Lemma 2, eq. (6), p. 2 (PDF p. 2), proved in the Appendix, eq. (15), p. 5, with the definition
of "almost all" on p. 2: "Almost all functions h satisfy `|2^{Ns} |Γ_{A_k}⟩ − 4^{−Nr} |1s⟩| ⪯
√2^{Ns+√Nr} |CHSH⟩^{⊗Nr}`, (6) for all k"; "the probability that h does not have that particular
property is lower than `2 exp(5Nr − 2^{√Nr}/4)`".

Assume `Ns + √Nr ≤ Nr + 2`. For a uniformly random `h : {0,1}^{Nr} → {0,1}^{Ns}`, the probability
that (6) fails for some `k` and some entry is less than `2 exp(5Nr − 2^{√Nr}/4)`.

**Formalization Note.** (1) Correction: the hypothesis `Ns + √Nr ≤ Nr + 2` is added. Without it
the lemma is false: at `Nr = 144`, `Ns = 160` (6) fails at the entry `a = b = x = y = 0` for every
`h`, while the claimed failure probability `2 exp(720 − 1024)` is below 1. (2) `Γ_a` is the
corrected vector (transposed tables); the facts the proof uses hold for either table. -/
theorem lemma_2 {Nr Ns : ℕ} (hN : (Ns : ℝ) + Real.sqrt Nr ≤ Nr + 2) :
    OAI.ThorpCompatibility.uniformProbability (fun h : Str Nr → Str Ns => ¬ SatisfiesEq6 h)
      < 2 * Real.exp (5 * Nr - (2 : ℝ) ^ Real.sqrt Nr / 4) := by sorry

end NoSignalPA
