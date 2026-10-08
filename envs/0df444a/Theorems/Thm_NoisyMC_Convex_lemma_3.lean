-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_3
-- name    : NoisyMC.Convex.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:47.516992+00:00
-- url     : https://prove2.me/theorems/df062aa5-86e5-467a-b4e6-1fed7e37c846
-- title:
--   Lemma 3 — the sampled noise has spectral norm O(σ√(np)) with probability 1 − O(n^{-10}), so Condition 1(a) holds
-- statement:
--   Under Assumption 1 (Bernoulli($p$) sampling of the entries and i.i.d. zero-mean noise with $\|E_{ij}\|_{\psi_2}\le\sigma$, independent of the sampling), suppose $n^2p\ge Cn\log^2n$ for a sufficiently large constant $C>0$. Then, with probability at least $1-O(n^{-10})$,
--
--   $$\|\mathcal P_\Omega(E)\|\lesssim\sigma\sqrt{np}.$$
--
--   As a result, Condition 1(a), $\|\mathcal P_\Omega(E)\|<\lambda/8$, holds with the same probability as long as $\lambda=C_\lambda\sigma\sqrt{np}$ for a sufficiently large constant $C_\lambda>0$.
--
--   This fixes the scale of the regularization parameter: $\lambda$ must dominate the spectral norm of the observed noise. The paper does not prove the lemma; it says that it follows from [CW15, Lemma 11] with a slight modification for asymmetric noise.
--
--   **Formalization Note.** The statement reads: there are $C,C',C_{\lambda0},C_{\rm fail}>0$ and $n_0$ such that for all $n\ge n_0$, $0<p\le1$, $\sigma>0$ and every model satisfying Assumption 1 with $n^2p\ge Cn\log^2n$,
--
--   1. $P\big(\|\mathcal P_\Omega(E)\|>C'\sigma\sqrt{np}\big)\le C_{\rm fail}n^{-10}$;
--   2. for every $C_\lambda\ge C_{\lambda0}$, $P\big(\|\mathcal P_\Omega(E)\|\ge C_\lambda\sigma\sqrt{np}/8\big)\le C_{\rm fail}n^{-10}$.
--
--   Probabilities of failure events are outer measures, so no measurability of the event is required. The "$\lesssim$" and $O(\cdot)$ constants are existential and come before $n$ and all data; $\log$ is the natural logarithm.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 12, Lemma 3 (proof omitted, p. 13)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 3 (p. 12). There are constants `C, C', C_λ0, C_fail > 0` and `n₀` such that for every
`n ≥ n₀`, `0 < p ≤ 1`, `σ > 0` and every sampling/noise model obeying Assumption 1 with
`n² p ≥ C n log² n`: with probability at least `1 − C_fail n^{-10}`, `‖P_Ω(E)‖ ≤ C' σ √(np)`;
and, as a result, for every `C_λ ≥ C_λ0`, with probability at least `1 − C_fail n^{-10}`,
`‖P_Ω(E)‖ < λ/8` for `λ = C_λ σ √(np)` (Condition 1(a)). -/
theorem lemma_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ Clam0 : ℝ, 0 < Clam0 ∧ ∃ Cfail : ℝ, 0 < Cfail ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∀ (p σ : ℝ), 0 < p → p ≤ 1 → 0 < σ →
    ∀ {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp) [IsProbabilityMeasure P]
      (δ : Fin n × Fin n → Ωp → Bool) (E : Fin n × Fin n → Ωp → ℝ),
      Assumption1 P p σ δ E →
      C * n * Real.log n ^ 2 ≤ (n : ℝ) ^ 2 * p →
      P {ω | ¬ spectralNorm (samplingProjection (obsSet δ ω) (noiseMatrix E ω)) ≤
          C' * σ * Real.sqrt (n * p)} ≤ ENNReal.ofReal (Cfail / (n : ℝ) ^ 10) ∧
      ∀ Clam : ℝ, Clam0 ≤ Clam →
        P {ω | ¬ spectralNorm (samplingProjection (obsSet δ ω) (noiseMatrix E ω)) <
          Clam * σ * Real.sqrt (n * p) / 8} ≤ ENNReal.ofReal (Cfail / (n : ℝ) ^ 10) := by sorry

end NoisyMC.Convex
