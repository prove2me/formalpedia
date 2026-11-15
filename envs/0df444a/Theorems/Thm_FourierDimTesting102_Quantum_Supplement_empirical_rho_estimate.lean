-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_empirical_rho_estimate
-- name    : FourierDimTesting102.Quantum.Supplement.empirical_rho_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:31:54.542058+00:00
-- url     : https://prove2.me/theorems/a8068cd2-1b22-423b-9df7-13be531ffb91
-- title:
--   Lemma 6.1 — $M=O(\frac{k\log(1/\beta)+\log(1/\delta)}{\beta^2})$ samples estimate $\rho_k(\mu)$ to within $\beta/2$
-- statement:
--   Let $\mu$ be any probability distribution on $\mathbb F_2^n$, let $0<\beta<1$ and $\delta>0$. There is an absolute constant $C$ such that for every
--
--   $$
--   M\ \ge\ C\,\frac{(k+1)\log(e/\beta)+\log(1/\delta)}{\beta^2},
--   $$
--
--   if $s_1,\dots,s_M$ are independent samples from $\mu$ and $\tilde\rho_k=\frac1M\min_{\dim W\le k}|\{i:s_i\notin W\}|$, then
--
--   $$
--   \Pr\Bigl[\,|\tilde\rho_k-\rho_k(\mu)|\le\frac\beta2\,\Bigr]\ge1-\delta ,
--   $$
--
--   where $\rho_k(\mu)=\min_{\dim W\le k}\mu(\overline W)$. For $k\ge1$ and $\beta\le1/2$ the threshold is of the order $\frac{k\log(1/\beta)+\log(1/\delta)}{\beta^2}$ of the source. The lemma is one of the two ingredients of the compression Theorem 6.1.
--
--   Differences from the source:
--   - generalization: set M = O((k log(1/β) + log(1/δ))/β²) → every M at least the threshold C((k+1) log(e/β) + log(1/δ))/β²; reason: the conclusion is claimed for all larger M, which contains the source’s choice of M
--   - reading: k log(1/β) in the sample bound → (k+1) log(e/β); reason: equal up to a constant factor for k ≥ 1 and β ≤ 1/2; the literal form fails at k = 0: for μ uniform on {0, e₁}, ρ₀(μ) = 1/2 and M = 1 gives |ρ̃ − ρ| = 1/2 > β/2 always, while C log(1/δ)/β² ≤ 1 for δ close to 1
--   - encoding: μ a probability distribution on F₂ⁿ; M independent samples → μ : V n → ℝ with μ ≥ 0 and ∑ μ = 1; the probability of an event is ∑_s ∏_i μ(s_i)·1[event]; reason: the exact law of M samples with replacement; point masses and zero weights allowed
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.28, Lemma 6.1 (proof pp.36–37, Appendix A)

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Lemma 6.1, p.28: there is an absolute constant `C` such that for every probability
distribution `μ` on `F₂ⁿ`, every `0 < β < 1`, `δ > 0`, and every number of samples
`M ≥ C((k+1) log(e/β) + log(1/δ))/β²`, the estimate `ρ̃_k` from `M` independent samples of `μ`
satisfies `Pr[|ρ̃_k − ρ_k(μ)| ≤ β/2] ≥ 1 − δ`. -/
theorem empirical_rho_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ) (μ : V n → ℝ) (β δ : ℝ), IsProbDist μ → 0 < β → β < 1 → 0 < δ →
      ∀ M : ℕ, C * (((k : ℝ) + 1) * Real.log (Real.exp 1 / β) + Real.log (1 / δ)) / β ^ 2 ≤ M →
        1 - δ ≤ sampleProb μ M (fun s => |rhoTilde k s - rhoK k μ| ≤ β / 2) := by sorry

end FourierDimTesting102.Quantum.Supplement
