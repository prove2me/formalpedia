-- Prove2me | Theorems.Thm_NonstatNV_lemma_5
-- name    : NonstatNV.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:53.170336+00:00
-- url     : https://prove2.me/theorems/abeb2f2e-3147-4d35-90e7-3955d9665be6
-- title:
--   Lemma 5 — the noise of the window average is at most $C_3T^{(3+v)/4}$ in expectation
-- statement:
--   Fix a scaling constant $\kappa>0$ and $\delta>0$. There is a constant $C_3\in(0,\infty)$, depending only on $\kappa$ and $\delta$, such that the following holds for every model satisfying the standing assumptions whose demand noise satisfies $\mathbb E[\exp((d-\mu)^2/\delta^2)]\le2$ for every $\mu\in[\mu_{\min},\mu_{\max}]$. For every horizon $T\ge1$, every $v\in[0,1]$ and every sequence of means $\mu_t\in[\mu_{\min},\mu_{\max}]$, with independent demands $d_s\sim D_{\mu_s}$, noise $\epsilon_s=d_s-\mu_s$ and $n=\lceil\kappa T^{(1-v)/2}\rceil$,
--
--   $$
--   \mathbb E\left[\sum_{t=n+1}^{T}\left|\frac1n\sum_{s=t-n}^{t-1}\epsilon_s\right|\right]\le C_3\,T^{(3+v)/4}.
--   $$
--
--   It bounds the stochastic half of the estimation error of the window average.
--
--   Differences from the source:
--   - reading: δ_s = inf{δ' ≥ 0 : E[e^{ε_s²/δ'²}] ≤ 2}, δ = max_s δ_s → a δ > 0 with E[exp((d − μ)²/δ²)] ≤ 2 for every μ ∈ [μmin, μmax]; reason: the constant must not depend on the instance, so the bound on the noise is uniform over the family; every admissible δ is allowed
--   - reading: there exists a universal constant C₃ → C₃ depends only on κ and δ and is chosen before the model, T, v and μ; reason: the proof's value is √(πδ²/(ρκ)) with a universal ρ
--   - encoding: E^{π^fixed}_D → the expectation under the product law of the demands; reason: the quantity does not involve the policy's orders
--   - encoding: n (the proof ignores the rounding) → n = ⌈κT^{(1−v)/2}⌉ with the ceiling; reason: the window size of the algorithm
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Lemma 5, p.37 (proof p.37)

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_NoiseMGFBound
import Definitions.Def_NonstatNV_Model_demandLaw
import Definitions.Def_NonstatNV_windowSize

open MeasureTheory

namespace NonstatNV

/-- **Lemma 5** (An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, p.37). There is a constant `C₃ ∈ (0, ∞)` such that, with
`n = ⌈κT^{(1−v)/2}⌉` and the noise `ε_s = d_s − μ_s`,
`E[Σ_{t=n+1}^{T} |(1/n) Σ_{s=t−n}^{t−1} ε_s|] ≤ C₃ T^{(3+v)/4}`.

**Formalization Note** `C₃` depends only on the scaling constant `κ > 0` and on a uniform bound
`δ > 0` with `E[exp(ε²/δ²)] ≤ 2` for every law of the family (the proof's `δ = max_s δ_s`, p.37; its
value is `√(πδ²/(ρκ))`). It is chosen before the model, `T`, `v` and `μ`. The expectation is over
independent demands `d_s ∼ D_{μ_s}` and does not depend on the policy. No variation hypothesis is
needed. -/
theorem lemma_5 (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ M : Model, M.Standing → M.NoiseMGFBound δ →
      ∀ T : ℕ, 1 ≤ T → ∀ v ∈ Set.Icc (0 : ℝ) 1, ∀ μ : ℕ → ℝ,
        (∀ t ∈ Finset.Icc 1 T, μ t ∈ Set.Icc M.μmin M.μmax) →
          ∫ ω, (∑ t ∈ Finset.Icc (windowSize T v κ + 1) T,
              |(1 / (windowSize T v κ : ℝ)) *
                ∑ s ∈ Finset.Ico (t - windowSize T v κ) t, (ω s - μ s)|) ∂(M.demandLaw μ) ≤
            C₃ * (T : ℝ) ^ ((3 + v) / 4) := by sorry

end NonstatNV
