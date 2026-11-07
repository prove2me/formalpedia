-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_4_7
-- name    : OnlineShadow.LogRate.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:16:51.569689+00:00
-- url     : https://prove2.me/theorems/1da1548a-75de-4063-b9ec-0129268c12f0
-- title:
--   Lemma 4.7 — the probability of a bad outcome
-- statement:
--   Run Algorithm 1 (ONLINESHADOWTOMOGRAPHY1) for $m$ rounds with accuracy $\varepsilon>0$, an integer mistake budget $K\ge1$ and logistic sharpness $0<\lambda\le n$, on $n$ copies of a $d\times d$ density matrix $\rho$ with $n\varepsilon^2>4608$, against any adaptive adversary.
--
--   **Lemma 4.7.** The probability over the course of the entire protocol that a bad outcome happens is at most
--   $$\frac{9216\,\lambda^2K}{n^2\varepsilon^2}+4(m+K)\,e^{-\lambda\varepsilon/16}.$$
--
--   With $\lambda=\Theta(\varepsilon n/\sqrt K)$ and $n=\Omega(\sqrt K\log(m+K)/\varepsilon^2)$ both terms are small constants, which with Lemma 4.4 proves Theorem 1.2.
--
--   **Formalization Note** Runs are indexed by outcome strings $\omega\in\{\text{flag},\text{pass}\}^{2(m+K)}$ with probabilities $\mathrm{Tr}(K_\omega\rho^{\otimes n}K_\omega^\dagger)$; the probability of a bad outcome is the total probability of the strings whose run performs a bad measurement.
--
--   Differences from the source:
--   - reading: no hypotheses printed → nε² > 4608, 0 < λ ≤ n, K ≥ 1, ε > 0; reason: the proof applies Lemma 4.5 (nε² > 4608) and Corollary 4.6 (0 < λ ≤ n); Algorithm 1 needs a positive budget; ε > 0 is Definition 1.1's (paper.md R7)
--   - generalization: Algorithm 1's parameters K = Θ(log(d)/ε²), λ = Θ(εn/√K) → any integer K ≥ 1 and any 0 < λ ≤ n, for every d; reason: the proof uses only 0 < λ ≤ n, nε² > 4608 and that at most K flags occur; the paper's parameters with a small leading constant in λ are instances
--   - encoding: the binary tree of internal histories, of depth ≤ 2(m + K) → outcome strings ω : Fin (2(m+K)) → Bool, unused coordinates carrying the trivial measurement; reason: the same probability space; Σ_ω Pr(ω) = 1 (paper.md R11)
--   - encoding: the protocol's states in the purified picture → probabilities computed on ρ^{⊗n} without purification; reason: purification does not change outcome probabilities
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 4.7, p. 13 (proof pp. 13–14)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_OnlineShadow_LogRate_alg1Prob
import Definitions.Def_OnlineShadow_LogRate_alg1Bad

open scoped ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 4.7** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.13; proof pp.13–14). Run Algorithm 1 with `m` rounds, accuracy `ε > 0`, mistake
budget `K ≥ 1` and sharpness `0 < λ ≤ n` on `n` copies of a density matrix `ρ`, with `n ε² > 4608`,
against any adaptive adversary. The probability that a bad outcome happens over the whole protocol is at
most `9216λ²K/(n²ε²) + 4(m + K)e^{−λε/16}`.

**Formalization Note** (paper.md R7, R11) The lemma prints no hypotheses; `n ε² > 4608` and
`0 < λ ≤ n` are those of Lemma 4.5 and Corollary 4.6, which its proof applies, `K ≥ 1` is a positive
budget, and `ε > 0` is Definition 1.1's. Runs are indexed by outcome strings `ω : Fin (2(m+K)) → Bool`
with probability `alg1Prob`; the probability of a bad outcome is the total probability of the strings
whose run performs a bad measurement (`alg1Bad`). -/
theorem lemma_4_7 {d : ℕ} (n m K : ℕ) (ε lam : ℝ) (hε : 0 < ε) (hK : 1 ≤ K)
    (hlam : 0 < lam) (hlamn : lam ≤ n) (hnε : 4608 < (n : ℝ) * ε ^ 2)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (adv : Adversary d) :
    haveI := Classical.propDecidable
    (∑ ω : Fin (2 * (m + K)) → Bool,
        if alg1Bad n m K ε lam adv ρ ω then alg1Prob n m K ε lam adv ρ ω else 0) ≤
      9216 * lam ^ 2 * K / ((n : ℝ) ^ 2 * ε ^ 2) + 4 * (m + K) * Real.exp (-(lam * ε / 16)) := by sorry

end OnlineShadow.LogRate
