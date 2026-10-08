-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_8
-- name    : NoisyMC.Convex.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:09.653933+00:00
-- url     : https://prove2.me/theorems/e5a41f53-74b2-43db-b577-dd4388af958c
-- title:
--   Lemma 8 — uniformly over (X, Y) obeying (26): ‖P_Ω(XYᵀ − M⋆) − p(XYᵀ − M⋆)‖ < λ/8
-- statement:
--   Let $M^\star\in\mathbb R^{n\times n}$ be rank $r\ge1$ and $\mu$-incoherent, with singular values between $\sigma_{\min}$ and $\sigma_{\max}$, condition number $\kappa$ and balanced factors $X^\star,Y^\star$. Let $\Omega$ follow Bernoulli($p$) sampling, $\sigma>0$, and $\lambda=C_\lambda\sigma\sqrt{np}$ for a constant $C_\lambda>0$. Suppose $n^2p\gg\kappa^4\mu^2r^2n\log^2n$ and $\sigma\sqrt{n(\log n)/p}\ll\sigma_{\min}/\kappa$. With probability exceeding $1-O(n^{-10})$,
--
--   $$\big\|\mathcal P_\Omega(XY^\top-M^\star)-p(XY^\top-M^\star)\big\|<\lambda/8$$
--
--   simultaneously for all $(X,Y)$ obeying
--
--   $$\max\{\|X-X^\star\|_{2,\infty},\|Y-Y^\star\|_{2,\infty}\}\le C_\infty\kappa\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac{n\log n}p}+\frac\lambda{p\,\sigma_{\min}}\Big)\max\{\|X^\star\|_{2,\infty},\|Y^\star\|_{2,\infty}\}.\qquad(26)$$
--
--   This is the Condition 1(b) half of Lemma 4: near the truth in the $\ell_{2,\infty}$ sense, the sampling operator concentrates around its mean uniformly.
--
--   **Formalization Note.** For every $C_\lambda>0$ and every $C_\infty>0$ (the constant of (26)) there are $C,c,C_{\rm fail}>0$ and $n_0$ such that, for all $n\ge n_0$ and all data with $n^2p\ge C\kappa^4\mu^2r^2n\log^2n$ and $\sigma\sqrt{n\log n/p}\le c\,\sigma_{\min}/\kappa$, the failure probability is at most $C_{\rm fail}n^{-10}$. Here "$\gg$" and "$\ll$" are read as in App. A of the paper ($A\gg B$: $A\ge CB$ for a sufficiently large constant $C$). The event involves only the sampling, so only Assumption 1(a) is assumed. Spectral norms throughout.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 32, Lemma 8; (26) p. 13; notation ≪, ≫ App. A p. 23

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 8 (p. 32). For every `C_λ > 0` and every `C_∞ > 0` (the constant of (26)) there are
constants `C, c, C_fail > 0` and `n₀` such that for every `n ≥ n₀`, every rank-`r` `µ`-incoherent
`M⋆` (SVD `S`, factors `X⋆, Y⋆`, `σ_min`, `κ`), every `0 < p ≤ 1`, `σ > 0` with
`n² p ≥ C κ⁴ µ² r² n log² n` and `σ √(n log n / p) ≤ c σ_min / κ`, and every Bernoulli(`p`)
sampling pattern (Assumption 1(a)), with `λ = C_λ σ √(np)`: with probability at least
`1 − C_fail n^{-10}`, `‖P_Ω(X Yᵀ − M⋆) − p (X Yᵀ − M⋆)‖ < λ/8` simultaneously for all `(X, Y)`
obeying (26):
`max{‖X − X⋆‖_{2,∞}, ‖Y − Y⋆‖_{2,∞}} ≤ C_∞ κ ((σ/σ_min) √(n log n / p) + λ/(p σ_min))
  max{‖X⋆‖_{2,∞}, ‖Y⋆‖_{2,∞}}`. -/
theorem lemma_8 :
    ∀ Clam : ℝ, 0 < Clam → ∀ Cinf : ℝ, 0 < Cinf →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ Cfail : ℝ, 0 < Cfail ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r : ℕ, 1 ≤ r →
    ∀ (μ : ℝ) (Mstar : RealMatrix n n) (S : SVD Mstar r), A0 S μ →
    ∀ (p σ : ℝ), 0 < p → p ≤ 1 → 0 < σ →
    ∀ {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp) [IsProbabilityMeasure P]
      (δ : Fin n × Fin n → Ωp → Bool),
      SamplingModel P p δ →
      C * condNum S ^ 4 * μ ^ 2 * r ^ 2 * n * Real.log n ^ 2 ≤ (n : ℝ) ^ 2 * p →
      σ * Real.sqrt (n * Real.log n / p) ≤ c * sigmaMin S / condNum S →
      P {ω | ¬ ∀ X Y : RealMatrix n r,
          max (twoInfNorm (X - Xstar S)) (twoInfNorm (Y - Ystar S)) ≤
            Cinf * condNum S *
              (σ / sigmaMin S * Real.sqrt (n * Real.log n / p) +
                Clam * σ * Real.sqrt (n * p) / (p * sigmaMin S)) *
              max (twoInfNorm (Xstar S)) (twoInfNorm (Ystar S)) →
          spectralNorm (samplingProjection (obsSet δ ω) (X * Y.transpose - Mstar) -
              p • (X * Y.transpose - Mstar)) <
            Clam * σ * Real.sqrt (n * p) / 8} ≤
        ENNReal.ofReal (Cfail / (n : ℝ) ^ 10) := by sorry

end NoisyMC.Convex
