-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_theorem_4_1
-- name    : LeakageRefresh.Continual.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:56.725641+00:00
-- url     : https://prove2.me/theorems/b278bede-92a3-4df7-9f08-0339ef3c47d1
-- title:
--   Theorem 4.1 — security of continual refreshing: $\delta(P_0^T,P_1^T)\le C\,T\,K^3q^{-1/9}\le C'\,T\,2^{6\lambda-n/9}$, also with the adversary's tape in the view
-- statement:
--   There are absolute real constants $C\ge1$ and $C'\ge1$ such that for all integers $n\ge2$, $T\ge0$ and $\lambda\ge0$, with $q=2^n-1$ and $K=2^{2\lambda}$, every adversary in the leakage model of Section 3 satisfies
--   $$\delta\big(P_0^T,P_1^T\big)\le C\cdot T\cdot K^3\cdot q^{-1/9}, \tag{4.1}$$
--   and the bound satisfies
--   $$C\cdot T\cdot K^3\cdot q^{-1/9}\le C'\cdot T\cdot2^{6\lambda-n/9}. \tag{4.2}$$
--   The same bound holds when the adversary's independent random tape is included in its view.
--
--   Here $P_s^T$ is the law of the complete leakage transcript $H_T=(Z_1,\dots,Z_T)$ when the secret $s$ is stored by the inner-product encoding and refreshed $T$ times by uniform invertible matrices (Definition 2.4), each party leaking $\lambda$ bits per refresh through functions of its own share and the refresh matrix chosen adaptively from earlier answers (Definitions 3.1–3.3). A deterministic adversary is a strategy; a randomized one is a measurable choice $\theta\mapsto\sigma_\theta$ of strategies from a probability space $(\Theta,\rho)$, and its view for the secret $s$ is the joint law of $(\theta,H_T)$. The theorem says the transcript is almost independent of the stored bit as soon as $2^{6\lambda}\ll2^{n/9}/T$.
--
--   Differences from the source:
--   - encoding: rounds $i\in\{1,\dots,T\}$ with incoming history $h\in\mathcal Z^{i-1}$ → `i : Fin T` is round $i+1$, with incoming history `Fin i → Answer lam`; reason: 0-based indexing of the same rounds and histories
--   - encoding: $P_s^T$, the distribution of the transcript of the real execution → `transcriptLaw σ s`: the point-probability function computed from the execution with $X_0\leftarrow\mu_s$ and independent uniform matrices; reason: a distribution on the finite set $\mathcal Z^T$ is its point-probability function
--   - reading: "every adversary in the leakage model of Sec. 3" and "the same bound holds when the adversary's independent random tape is included in its view" → deterministic strategies (first conjunct) and, for every probability space $(\Theta,\rho)$ in any universe and every measurable $\sigma:\Theta\to$ strategies, $\mathrm{TV}$ (sup over measurable sets) of the joint laws of $(\theta,H_T)$ (second conjunct); reason: §3.4 shows every randomized adversary of Sec. 3, including private auxiliary randomness presampled per (round, history, matrix), is a random deterministic strategy; App. A defines the distance of the tape-and-view laws
--   - encoding: $K^3q^{-1/9}$ and $2^{6\lambda-n/9}$ → `((2:ℝ)^(2*lam))^3 * ((2:ℝ)^n - 1)^(-(1/9:ℝ))` and `(2:ℝ)^(6*lam - n/9)` with `Real.rpow`; reason: real exponents
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), pp. 27–28, Theorem 4.1 (proof p. 45)

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory

namespace LeakageRefresh.Continual

/-- **Theorem 4.1 (Security of continual refreshing).** There are real constants `C ≥ 1`,
`C′ ≥ 1` such that for all `n ≥ 2`, `T ≥ 0`, `λ ≥ 0` (here `lam`), with `q = 2ⁿ − 1` and
`K = 2^{2λ}`:
* (4.1) every deterministic adaptive strategy `σ` gives `δ(P₀ᵀ, P₁ᵀ) ≤ C · T · K³ · q^{−1/9}`;
* the same bound holds for the joint law of the adversary's tape `θ ←$ ρ` and the transcript,
  for every probability space `(Θ, ρ)` and measurable choice `θ ↦ σ θ` of deterministic
  strategies;
* (4.2) `C · T · K³ · q^{−1/9} ≤ C′ · T · 2^{6λ − n/9}`. -/
theorem theorem_4_1.{u} :
    ∃ C C' : ℝ, 1 ≤ C ∧ 1 ≤ C' ∧
      ∀ n T lam : ℕ, 2 ≤ n →
        (∀ σ : Strategy n T lam,
          statDist (transcriptLaw σ 0) (transcriptLaw σ 1) ≤
            C * (T : ℝ) * ((2 : ℝ) ^ (2 * lam)) ^ 3 * ((2 : ℝ) ^ n - 1) ^ (-(1 / 9 : ℝ))) ∧
        (∀ (Θ : Type u) [MeasurableSpace Θ] (ρ : Measure Θ) [IsProbabilityMeasure ρ]
            (σ : Θ → Strategy n T lam) (hσ : Measurable σ),
          FoundationsRL.DECLower.tvDist (viewLaw ρ σ hσ 0) (viewLaw ρ σ hσ 1) ≤
            C * (T : ℝ) * ((2 : ℝ) ^ (2 * lam)) ^ 3 * ((2 : ℝ) ^ n - 1) ^ (-(1 / 9 : ℝ))) ∧
        C * (T : ℝ) * ((2 : ℝ) ^ (2 * lam)) ^ 3 * ((2 : ℝ) ^ n - 1) ^ (-(1 / 9 : ℝ)) ≤
          C' * (T : ℝ) * (2 : ℝ) ^ (6 * (lam : ℝ) - (n : ℝ) / 9) := by sorry

end LeakageRefresh.Continual
