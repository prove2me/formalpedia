-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_A_1
-- name    : GapAgnosticGS.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:29:17.599819+00:00
-- url     : https://prove2.me/theorems/c5d89995-c94c-4501-8a8c-e90879f7de58
-- title:
--   Lemma A.1 — phase estimation amplitudes and the $8/\pi^2$ success bound
-- statement:
--   Let $W$ be a unitary on a finite-dimensional space, $t\ge2$, $N_t=2^t$, and let $|v_\varphi\rangle$ be a unit eigenvector with $W|v_\varphi\rangle=e^{2\pi i\varphi}|v_\varphi\rangle$, $\varphi\in[0,1)$. Then the standard $t$-qubit phase estimation satisfies
--
--   $$\mathrm{QPE}_t(W)|0^t\rangle|v_\varphi\rangle=\sum_{y=0}^{N_t-1}a_y(\varphi)|y\rangle|v_\varphi\rangle,\qquad a_y(\varphi)=\frac1{N_t}\sum_{m=0}^{N_t-1}e^{2\pi i m(\varphi-y/N_t)} ,$$
--
--   and the measured outcome $Y$ satisfies
--
--   $$\Pr\Big[\mathrm{dist}_T\Big(\frac Y{N_t},\varphi\Big)\le\frac1{N_t}\Big]\ge\frac8{\pi^2},\qquad \mathrm{dist}_T(x,y)=\min_{k\in\mathbb Z}|x-y-k| .$$
--
--   This is the precision guarantee behind the threshold tests of Lemma 3.5.
--
--   Differences from the source:
--   - encoding: the standard t-qubit QPE_t unitary applied to |0^t⟩|v_φ⟩ → the published QAlgorithms.phaseEstimationState t W v, outcome y read as the integer bitsToNat y (most significant bit first); reason: the platform's definition of the same circuit
--   - encoding: Pr[dist_T(Y/N_t, φ) ≤ 1/N_t] with dist_T = min_k |x − y − k| → the sum of the outcome probabilities marginalFst over the y with ∃ k ∈ ℤ, |y/N_t − φ − k| ≤ 1/N_t; reason: the minimum over k is attained, so the two conditions agree
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), App. A.1, Lemma A.1 (Theorem 11 of [BHMT02]) and the standing text before it, p.27 (PDF p.28)

import Definitions.Def_QAlgorithms_Defs_Fourier
open QAlgorithms

namespace GapAgnosticGS

open Classical in
/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Appendix A.1, Lemma A.1 (Theorem 11 of [BHMT02]), p.27 (PDF p.28), with the standing
text before it: "Let T be a t-qubit phase register, where t ≥ 2, and let N_t := 2^t. For
x, y ∈ [0, 1), let dist_T(x, y) := min_{k∈ℤ} |x − y − k| denote circular distance modulo one.
Lemma A.1. Let W be a unitary and let |v_φ⟩ be a normalized eigenvector satisfying
W|v_φ⟩ = e^{2πiφ}|v_φ⟩ for φ ∈ [0, 1). Then the standard t-qubit QPE_t unitary satisfies
QPE_t(W)|0^t⟩|v_φ⟩ = Σ_{y=0}^{N_t−1} a_y(φ)|y⟩|v_φ⟩, where
a_y(φ) = (1/N_t) Σ_{m=0}^{N_t−1} e^{2πim(φ−y/N_t)}. Moreover, if Y denotes the phase-register
measurement outcome, then Pr[dist_T(Y/N_t, φ) ≤ 1/N_t] ≥ 8/π²."

**Formalization Note.** `QPE_t(W)|0^t⟩|v⟩` is the published `QAlgorithms.phaseEstimationState t W v`
(Hadamards = `F_{2^t}` on `|0^t⟩`, the controlled powers `Σ_y |y⟩⟨y| ⊗ W^y`, then `F_{2^t}^{−1}`);
the outcome `y` is the integer `bitsToNat y` (most significant bit first). The probability of the
outcome `y` is `marginalFst`. `dist_T(x, φ) ≤ 1/N_t` is written `∃ k ∈ ℤ, |x − φ − k| ≤ 1/N_t`
(the minimum over `k` is attained). -/
theorem lemma_A_1 {κ : Type} [Fintype κ] [DecidableEq κ] (W : Matrix κ κ ℂ)
    (hW : W ∈ Matrix.unitaryGroup κ ℂ) (t : ℕ) (ht : 2 ≤ t) (v : EuclideanSpace ℂ κ)
    (hv : ‖v‖ = 1) (φ : ℝ) (hφ : φ ∈ Set.Ico 0 1)
    (heig : act W v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    let N : ℕ := 2 ^ t
    let a : ℕ → ℂ := fun y => (1 / (N : ℂ)) * ∑ m ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * ((φ : ℂ) - (y : ℂ) / (N : ℂ)))
    phaseEstimationState t W v = ∑ y : Qubits t, a (bitsToNat y) • tensorVec (ket y) v ∧
    8 / Real.pi ^ 2 ≤ ∑ y : Qubits t,
      if ∃ k : ℤ, |(bitsToNat y : ℝ) / N - φ - k| ≤ 1 / N then
        marginalFst (phaseEstimationState t W v) y
      else 0 := by sorry

end GapAgnosticGS
