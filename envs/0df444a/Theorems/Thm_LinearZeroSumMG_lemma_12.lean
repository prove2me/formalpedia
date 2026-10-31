-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_12
-- name    : LinearZeroSumMG.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:20.666425+00:00
-- url     : https://prove2.me/theorems/fa528c38-015a-403d-a285-7dd275910659
-- title:
--   Lemma 12, p.30 — self-normalized bound $\|\sum_s\phi_s\epsilon_s\|^2_{\Lambda_t^{-1}}\le2\sigma^2\log(\det(\Lambda_t)^{1/2}\det(\Lambda_0)^{-1/2}/\delta)$
-- statement:
--   **Lemma 12 (Concentration for self-normalized processes).** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with filtration $(\mathcal F_t)_{t\ge0}$. Let $(\epsilon_t)_{t\ge1}$ be real random variables with $\epsilon_t$ $\mathcal F_t$-measurable and integrable, such that conditionally on $\mathcal F_{t-1}$ it has mean zero and is $\sigma$-sub-Gaussian:
--   $$
--   \mathbb E[\epsilon_t\mid\mathcal F_{t-1}]=0,\qquad\mathbb E[e^{\lambda\epsilon_t}\mid\mathcal F_{t-1}]\le e^{\lambda^2\sigma^2/2}\quad\text{a.s., for all }\lambda\in\mathbb R .
--   $$
--   Let $(\phi_t)_{t\ge1}$ be $\mathbb R^d$-valued with $\phi_t$ $\mathcal F_{t-1}$-measurable, let $\Lambda_0$ be positive definite and $\Lambda_t=\Lambda_0+\sum_{s=1}^t\phi_s\phi_s^\top$. Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--   $$
--   \Big\|\sum_{s=1}^t\phi_s\epsilon_s\Big\|^2_{\Lambda_t^{-1}}\le2\sigma^2\log\Big[\frac{\det(\Lambda_t)^{1/2}\det(\Lambda_0)^{-1/2}}{\delta}\Big]\qquad\text{for all }t\ge0 .
--   $$
--
--   This is the self-normalized martingale bound of Abbasi-Yadkori, Pál and Szepesvári (2011, Theorem 1); Lemma 2 applies it to each fixed pair of the $\varepsilon$-net.
--
--   Differences from the source:
--   - generalization: {ε_t} "generating the filtration {𝓕_t}" → ε_t adapted to an arbitrary filtration 𝓕 (𝓕_t-measurable); reason: the natural filtration of the process is a special case
--   - encoding: "ε_t|𝓕_{t−1} is zero mean and σ-subGaussian" → 𝔼[ε_t | 𝓕_{t−1}] = 0 and 𝔼[exp(λε_t) | 𝓕_{t−1}] ≤ exp(λ²σ²/2) a.s. for all λ, with ε_t and exp(λε_t) integrable; reason: the standard definition of conditional sub-Gaussianity; integrability makes the conditional expectations meaningful
--   - encoding: "with probability at least 1 − p" → the outer measure of the set of sample points where the bound fails is at most p; reason: no measurability of the event is needed; same statement when it is measurable
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 12, p.30

import Mathlib
import Definitions.Def_LinearZeroSumMG_clip

open MeasureTheory ProbabilityTheory Matrix

namespace LinearZeroSumMG

/-- **Lemma 12 (Concentration for Self-normalized Processes).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 12, p.30: "Suppose `{ε_t}_{t≥1}`
is a scalar stochastic process generating the filtration `{𝓕_t}_{t≥0}`, and `ε_t|𝓕_{t−1}` is zero mean
and `σ`-subGaussian. Let `{φ_t}_{t≥1}` be an `ℝ^d`-valued stochastic process with `φ_t ∈ 𝓕_{t−1}`.
Suppose `Λ₀ ∈ ℝ^{d×d}` is positive definite, and `Λ_t = Λ₀ + ∑_{s=1}^t φ_sφ_sᵀ`. Then for each
`δ ∈ (0, 1)`, with probability at least `1 − δ`, we have
`‖∑_{s=1}^t φ_sε_s‖²_{Λ_t⁻¹} ≤ 2σ² log[det(Λ_t)^{1/2} det(Λ₀)^{−1/2} / δ]`, `∀t ≥ 0`."

On a probability space with filtration `𝓕`, let `e_t` (the paper's `ε_t`) be `𝓕_t`-measurable and
integrable, `ψ_t` (the paper's `φ_t`) be `𝓕_{t−1}`-measurable, for `t ≥ 1`, with
`𝔼[e_t | 𝓕_{t−1}] = 0` and `𝔼[exp(λe_t) | 𝓕_{t−1}] ≤ exp(λ²σ²/2)` a.s. for every `λ ∈ ℝ`
(`exp(λe_t)` integrable). Then for `δ ∈ (0, 1)` the (outer) probability that
`‖∑_{s=1}^t ψ_s e_s‖²_{Λ_t⁻¹} > 2σ² log(det(Λ_t)^{1/2} det(Λ₀)^{−1/2}/δ)` for some `t ≥ 0` is at most `δ`.

**Formalization Note**
- "Generating the filtration" is generalized to "adapted to the filtration".
- `σ`-sub-Gaussianity is the conditional moment-generating-function bound, stated through
  conditional expectations (with integrability of `exp(λe_t)`, without which the conditional
  expectation would be `0`).
- "With probability at least `1 − δ`" bounds the outer measure of the failure set by `δ`, so no
  measurability of that set is needed. No standard-Borel assumption on `Ω` is made. -/
theorem lemma_12 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›) {d : ℕ} (e : ℕ → Ω → ℝ) (ψ : ℕ → Ω → Fin d → ℝ)
    (σ : ℝ) (Λ₀ : Matrix (Fin d) (Fin d) ℝ) (hΛ₀ : Λ₀.PosDef)
    (he_meas : ∀ t, 1 ≤ t → Measurable[𝓕 t] (e t))
    (hψ_meas : ∀ t, 1 ≤ t → Measurable[𝓕 (t - 1)] (ψ t))
    (he_int : ∀ t, 1 ≤ t → Integrable (e t) μ)
    (he_mean : ∀ t, 1 ≤ t → μ[e t | 𝓕 (t - 1)] =ᵐ[μ] 0)
    (he_subG : ∀ t, 1 ≤ t → ∀ l : ℝ,
      Integrable (fun ω => Real.exp (l * e t ω)) μ ∧
      μ[fun ω => Real.exp (l * e t ω) | 𝓕 (t - 1)] ≤ᵐ[μ] fun _ => Real.exp (l ^ 2 * σ ^ 2 / 2))
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    μ {ω | ∃ t : ℕ,
        2 * σ ^ 2 * Real.log (Real.sqrt (Λ₀ + ∑ s ∈ Finset.Icc 1 t,
              vecMulVec (ψ s ω) (ψ s ω)).det * (Real.sqrt Λ₀.det)⁻¹ / δ) <
          wNorm (Λ₀ + ∑ s ∈ Finset.Icc 1 t, vecMulVec (ψ s ω) (ψ s ω))⁻¹
            (∑ s ∈ Finset.Icc 1 t, e s ω • ψ s ω) ^ 2} ≤ ENNReal.ofReal δ := by sorry

end LinearZeroSumMG
