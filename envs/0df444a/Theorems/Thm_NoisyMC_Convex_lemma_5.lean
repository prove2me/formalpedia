-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_5
-- name    : NoisyMC.Convex.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:27.602411+00:00
-- url     : https://prove2.me/theorems/a0e12029-189d-4a57-8489-5fd8357b6933
-- title:
--   Lemma 5 — the gradient-descent iterates of Algorithm 1 stay close to (X⋆, Y⋆) in F, operator and ℓ2,∞ norms, and some iterate has ‖∇f‖_F ≤ n^{-5}(λ/p)√σ_min
-- statement:
--   Instate the notation and hypotheses of Theorem 2, and run Algorithm 1 on the observed data from $(X^0,Y^0)=(X^\star,Y^\star)$ with step size $\eta\asymp1/(n\kappa^3\sigma_{\max})$ for $t_0=n^{18}$ iterations. For each $t$ let $H^t$ be an orthogonal matrix minimizing $(\|X^tR-X^\star\|_F^2+\|Y^tR-Y^\star\|_F^2)^{1/2}$ over orthogonal $R$ (28). With probability at least $1-O(n^{-3})$, for all $0\le t\le t_0$,
--
--   $$\max\{\|X^tH^t-X^\star\|_F,\|Y^tH^t-Y^\star\|_F\}\le C_F\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac np}+\frac\lambda{p\sigma_{\min}}\Big)\|X^\star\|_F,\qquad(29a)$$
--
--   $$\max\{\|X^tH^t-X^\star\|,\|Y^tH^t-Y^\star\|\}\le C_{\rm op}\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac np}+\frac\lambda{p\sigma_{\min}}\Big)\|X^\star\|,\qquad(29b)$$
--
--   $$\max\{\|X^tH^t-X^\star\|_{2,\infty},\|Y^tH^t-Y^\star\|_{2,\infty}\}\le C_\infty\kappa\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac{n\log n}p}+\frac\lambda{p\sigma_{\min}}\Big)\max\{\|X^\star\|_{2,\infty},\|Y^\star\|_{2,\infty}\},\qquad(29c)$$
--
--   $$\min_{0\le t<t_0}\|\nabla f(X^t,Y^t)\|_F\le\frac1{n^5}\,\frac\lambda p\sqrt{\sigma_{\min}},\qquad(30)$$
--
--   where $C_F,C_{\rm op},C_\infty>0$ are absolute constants.
--
--   All iterates of gradient descent, started at the truth, remain close to the true factors, and some iterate is an approximate critical point. These are the two inputs Lemma 2 needs.
--
--   **Formalization Note.** Quantifiers: there is $C_{\lambda0}>0$ such that for every $C_\lambda\ge C_{\lambda0}$ there are $C,c$ (Theorem 2's sample-size and noise constants), $C_F,C_{\rm op},C_\infty$, a step-size constant $c_\eta>0$, $C_{\rm fail}>0$ and $n_0$. The step size is pinned as $\eta=c_\eta/(n\kappa^3\sigma_{\max})$, the weakest reading of "$\eta\asymp1/(n\kappa^3\sigma_{\max})$" that the proof of Theorem 2 needs. The bounds (29a)–(29c) are required for every minimizer $H^t$ of (28), since the minimizer need not be unique. (30) is stated as "some $t<t_0$ has $\|\nabla f(X^t,Y^t)\|_F\le n^{-5}(\lambda/p)\sqrt{\sigma_{\min}}$". The exponent 18 and the factor $n^{-5}$ are the paper's.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 14, Lemma 5, (28)–(30); Algorithm 1 p. 13

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 5 (p. 14). Under the notation and hypotheses of Theorem 2 (some `C_λ0 > 0`, every
`C_λ ≥ C_λ0`, then constants `C, c` of the sample-size and noise conditions), there are absolute
constants `C_F, C_op, C_∞ > 0`, a step-size constant `c_η > 0`, a constant `C_fail > 0` and `n₀`
such that, for every `n ≥ n₀`, every rank-`r` `µ`-incoherent `M⋆`, every `0 < p ≤ 1`, `σ > 0`
and every model obeying Assumption 1 with `n² p ≥ C κ⁴ µ² r² n log³ n` and
`σ √(n/p) ≤ c σ_min / √(κ⁴ µ r log n)`: with `λ = C_λ σ √(np)`, `η = c_η / (n κ³ σ_max)` and
`t₀ = n¹⁸`, the iterates `(Xᵗ, Yᵗ)` of Algorithm 1 run on the observed data satisfy, with
probability at least `1 − C_fail n^{-3}`, for every `0 ≤ t ≤ t₀` and every minimizer `Hᵗ` of (28),
(29a) `max{‖XᵗHᵗ − X⋆‖_F, ‖YᵗHᵗ − Y⋆‖_F} ≤ C_F ((σ/σ_min)√(n/p) + λ/(pσ_min)) ‖X⋆‖_F`,
(29b) `max{‖XᵗHᵗ − X⋆‖, ‖YᵗHᵗ − Y⋆‖} ≤ C_op ((σ/σ_min)√(n/p) + λ/(pσ_min)) ‖X⋆‖`,
(29c) `max{‖XᵗHᵗ − X⋆‖_{2,∞}, ‖YᵗHᵗ − Y⋆‖_{2,∞}}
  ≤ C_∞ κ ((σ/σ_min)√(n log n/p) + λ/(pσ_min)) max{‖X⋆‖_{2,∞}, ‖Y⋆‖_{2,∞}}`,
and (30) `min_{0 ≤ t < t₀} ‖∇f(Xᵗ, Yᵗ)‖_F ≤ n^{-5} (λ/p) √σ_min`. -/
theorem lemma_5 :
    ∃ Clam0 : ℝ, 0 < Clam0 ∧ ∀ Clam : ℝ, Clam0 ≤ Clam →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∃ CF : ℝ, 0 < CF ∧ ∃ Cop : ℝ, 0 < Cop ∧ ∃ Cinf : ℝ, 0 < Cinf ∧ ∃ ceta : ℝ, 0 < ceta ∧
    ∃ Cfail : ℝ, 0 < Cfail ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r : ℕ, 1 ≤ r →
    ∀ (μ : ℝ) (Mstar : RealMatrix n n) (S : SVD Mstar r), A0 S μ →
    ∀ (p σ : ℝ), 0 < p → p ≤ 1 → 0 < σ →
    ∀ {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp) [IsProbabilityMeasure P]
      (δ : Fin n × Fin n → Ωp → Bool) (E : Fin n × Fin n → Ωp → ℝ),
      Assumption1 P p σ δ E →
      C * condNum S ^ 4 * μ ^ 2 * r ^ 2 * n * Real.log n ^ 3 ≤ (n : ℝ) ^ 2 * p →
      σ * Real.sqrt (n / p) ≤
        c * sigmaMin S / Real.sqrt (condNum S ^ 4 * μ * r * Real.log n) →
      let lam : ℝ := Clam * σ * Real.sqrt (n * p)
      let η : ℝ := ceta / (n * condNum S ^ 3 * sigmaMax S)
      let t0 : ℕ := n ^ 18
      P {ω |
        let iter := gdIter (obsSet δ ω) (dataMatrix Mstar E ω) lam p η (Xstar S) (Ystar S)
        ¬ ((∀ t : ℕ, t ≤ t0 → ∀ H : Matrix (Fin r) (Fin r) ℝ,
              IsAlignment (Xstar S) (Ystar S) (iter t).1 (iter t).2 H →
              max (frobeniusNorm ((iter t).1 * H - Xstar S))
                  (frobeniusNorm ((iter t).2 * H - Ystar S)) ≤
                CF * (σ / sigmaMin S * Real.sqrt (n / p) + lam / (p * sigmaMin S)) *
                  frobeniusNorm (Xstar S) ∧
              max (spectralNorm ((iter t).1 * H - Xstar S))
                  (spectralNorm ((iter t).2 * H - Ystar S)) ≤
                Cop * (σ / sigmaMin S * Real.sqrt (n / p) + lam / (p * sigmaMin S)) *
                  spectralNorm (Xstar S) ∧
              max (twoInfNorm ((iter t).1 * H - Xstar S))
                  (twoInfNorm ((iter t).2 * H - Ystar S)) ≤
                Cinf * condNum S *
                  (σ / sigmaMin S * Real.sqrt (n * Real.log n / p) + lam / (p * sigmaMin S)) *
                  max (twoInfNorm (Xstar S)) (twoInfNorm (Ystar S))) ∧
            ∃ t : ℕ, t < t0 ∧
              gradNorm (obsSet δ ω) (dataMatrix Mstar E ω) lam p (iter t).1 (iter t).2 ≤
                1 / (n : ℝ) ^ 5 * (lam / p) * Real.sqrt (sigmaMin S))} ≤
        ENNReal.ofReal (Cfail / (n : ℝ) ^ 3) := by sorry

end NoisyMC.Convex
