-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_compression_preserves_estimate
-- name    : FourierDimTesting102.Quantum.Supplement.compression_preserves_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:32:40.915198+00:00
-- url     : https://prove2.me/theorems/f76c039b-05f1-40ae-bccf-7a61032f8766
-- title:
--   Lemma 6.2 — a random linear map to $O(k\log\frac Mk+\log\frac1\delta)$ dimensions preserves $\tilde\rho_k$ exactly
-- statement:
--   Fix a list of $M$ vectors $s_1,\dots,s_M\in\mathbb F_2^n$ (for instance, samples drawn as in Lemma 6.1) and $\delta>0$. There is an absolute constant $C$ such that for every
--
--   $$
--   r\ \ge\ C\Bigl((k+1)\log\frac{eM}{k+1}+\log\frac1\delta\Bigr),
--   $$
--
--   a uniformly random linear map $X:\mathbb F_2^n\to\mathbb F_2^r$ satisfies, with probability at least $1-\delta$,
--
--   $$
--   \tilde\rho_k=\tilde\rho_{k,X},
--   $$
--
--   where $\tilde\rho_{k,X}$ is the estimate of Lemma 6.1 computed from $Xs_1,\dots,Xs_M$. For $k\ge1$ and $M\ge ek$ (as for the $M$ of Lemma 6.1) the threshold is of the order $k\log\frac Mk+\log\frac1\delta$ of the source.
--
--   Differences from the source:
--   - generalization: a set of M samples from µ, with M in Lemma 6.1 → any M and any fixed list s : Fin M → V n; reason: the statement is for fixed samples and µ plays no role; every realized sample list and the M of Lemma 6.1 are instances
--   - generalization: r = O(k log(M/k) + log(1/δ)) (one r) → every r at least the threshold; reason: the conclusion is claimed for all larger r, which contains the source’s choice
--   - reading: k log(M/k) → (k+1) log(eM/(k+1)); reason: equal up to a constant factor for k ≥ 1 and M ≥ ek, the source’s regime; the literal form fails at M = k+1: k+1 independent samples give ρ̃_k = 1/M, every compressed estimate with r ≤ k is 0, yet k log((k+1)/k) + log(1/δ) ≤ 1 + log(1/δ) permits r ≤ k for large k
--   - encoding: a random linear map X : F₂ⁿ → F₂ʳ → X uniform on r × n matrices over ZMod 2; reason: independent uniform entries, singular maps included
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.28, Lemma 6.2 (proof pp.37–38, Appendix A)

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Lemma 6.2, p.28: there is an absolute constant `C` such that for every fixed list of `M`
vectors `s₁, …, s_M ∈ F₂ⁿ`, every `δ > 0` and every `r ≥ C((k+1) log(eM/(k+1)) + log(1/δ))`, a
uniformly random linear map `X : F₂ⁿ → F₂ʳ` satisfies `ρ̃_{k,X} = ρ̃_k` with probability at least
`1 − δ`, where `ρ̃_{k,X}` is the estimate computed from `X s₁, …, X s_M`. -/
theorem compression_preserves_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k M r : ℕ) (δ : ℝ), 0 < δ →
      C * (((k : ℝ) + 1) * Real.log (Real.exp 1 * M / ((k : ℝ) + 1)) + Real.log (1 / δ)) ≤ r →
      ∀ s : Fin M → V n,
        1 - δ ≤ unifProb (fun X : LinMap n r => rhoTilde k (compress X s) = rhoTilde k s) := by sorry

end FourierDimTesting102.Quantum.Supplement
