-- Prove2me | Theorems.Thm_NoisyMC_Convex_lemma_4
-- name    : NoisyMC.Convex.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:16.147559+00:00
-- url     : https://prove2.me/theorems/c5ca5114-dd87-4522-8bbb-5ec78c60c3b1
-- title:
--   Lemma 4 — under Theorem 2's assumptions, Conditions 1(b) and 2 (c_inj = 1/(32κ)) hold simultaneously for all (X, Y) obeying (26) w.p. 1 − O(n^{-10})
-- statement:
--   Under the assumptions of Theorem 2, with probability exceeding $1-O(n^{-10})$ we have
--
--   $$\big\|\mathcal P_\Omega(XY^\top-M^\star)-p(XY^\top-M^\star)\big\|<\lambda/8\qquad\text{(Condition 1(b))}$$
--
--   $$\frac1p\|\mathcal P_\Omega(H)\|_F^2\ge\frac1{32\kappa}\|H\|_F^2\ \text{ for all }H\in T\qquad\text{(Condition 2 with }c_{\rm inj}=(32\kappa)^{-1})$$
--
--   simultaneously for all $(X,Y)$ obeying
--
--   $$\max\{\|X-X^\star\|_{2,\infty},\|Y-Y^\star\|_{2,\infty}\}\le C_\infty\kappa\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac{n\log n}p}+\frac\lambda{p\,\sigma_{\min}}\Big)\max\{\|X^\star\|_{2,\infty},\|Y^\star\|_{2,\infty}\}.\qquad(26)$$
--
--   Here $T$ is the tangent space of $XY^\top$ and $C_\infty>0$ is an absolute constant. The assumptions of Theorem 2 are: $M^\star$ is rank $r$ and $\mu$-incoherent with condition number $\kappa$; Assumption 1 holds; $\lambda=C_\lambda\sigma\sqrt{np}$ with $C_\lambda$ large enough; $n^2p\ge C\kappa^4\mu^2r^2n\log^3n$; and $\sigma\sqrt{n/p}\le c\,\sigma_{\min}/\sqrt{\kappa^4\mu r\log n}$.
--
--   Because the bounds hold uniformly over a neighbourhood of the truth, they apply to points that depend on $\Omega$, such as the gradient-descent iterates of Algorithm 1.
--
--   **Formalization Note.** The quantifiers follow Theorem 2: there is $C_{\lambda0}>0$ such that for every $C_\lambda\ge C_{\lambda0}$ and every $C_\infty>0$ there are $C,c,C_{\rm fail}>0$ and $n_0$ with failure probability at most $C_{\rm fail}n^{-10}$ for all $n\ge n_0$ and all data. $C_\infty$ is universally quantified because in the proof of Theorem 2 it is the constant produced by Lemma 5; $C$, $c$ may depend on it, as in Remark 8 and Lemma 8 of the paper. The tangent space is $\{XA^\top+BY^\top\}$, as in (80).
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 13, Lemma 4, (26)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Lemma 4 (p. 13). Under the assumptions of Theorem 2 — with the quantifiers of Theorem 2: some
`C_λ0 > 0`, every `C_λ ≥ C_λ0`, and, for every absolute constant `C_∞ > 0` of (26), some
constants `C, c, C_fail > 0` and `n₀` — the following holds for every `n ≥ n₀`, every rank-`r`
`µ`-incoherent `M⋆`, every `0 < p ≤ 1`, `σ > 0` and every model obeying Assumption 1 with
`n² p ≥ C κ⁴ µ² r² n log³ n` and `σ √(n/p) ≤ c σ_min / √(κ⁴ µ r log n)`, with
`λ = C_λ σ √(np)`: with probability at least `1 − C_fail n^{-10}`, simultaneously for all `(X, Y)`
obeying (26),
`‖P_Ω(X Yᵀ − M⋆) − p (X Yᵀ − M⋆)‖ < λ/8` (Condition 1(b)) and
`p⁻¹ ‖P_Ω(H)‖_F² ≥ (32κ)⁻¹ ‖H‖_F²` for all `H` in the tangent space of `X Yᵀ`
(Condition 2 with `c_inj = (32κ)⁻¹`). -/
theorem lemma_4 :
    ∃ Clam0 : ℝ, 0 < Clam0 ∧ ∀ Clam : ℝ, Clam0 ≤ Clam → ∀ Cinf : ℝ, 0 < Cinf →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ Cfail : ℝ, 0 < Cfail ∧
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r : ℕ, 1 ≤ r →
    ∀ (μ : ℝ) (Mstar : RealMatrix n n) (S : SVD Mstar r), A0 S μ →
    ∀ (p σ : ℝ), 0 < p → p ≤ 1 → 0 < σ →
    ∀ {Ωp : Type} [MeasurableSpace Ωp] (P : Measure Ωp) [IsProbabilityMeasure P]
      (δ : Fin n × Fin n → Ωp → Bool) (E : Fin n × Fin n → Ωp → ℝ),
      Assumption1 P p σ δ E →
      C * condNum S ^ 4 * μ ^ 2 * r ^ 2 * n * Real.log n ^ 3 ≤ (n : ℝ) ^ 2 * p →
      σ * Real.sqrt (n / p) ≤
        c * sigmaMin S / Real.sqrt (condNum S ^ 4 * μ * r * Real.log n) →
      P {ω | ¬ ∀ X Y : RealMatrix n r,
          max (twoInfNorm (X - Xstar S)) (twoInfNorm (Y - Ystar S)) ≤
            Cinf * condNum S *
              (σ / sigmaMin S * Real.sqrt (n * Real.log n / p) +
                Clam * σ * Real.sqrt (n * p) / (p * sigmaMin S)) *
              max (twoInfNorm (Xstar S)) (twoInfNorm (Ystar S)) →
          spectralNorm (samplingProjection (obsSet δ ω) (X * Y.transpose - Mstar) -
              p • (X * Y.transpose - Mstar)) <
            Clam * σ * Real.sqrt (n * p) / 8 ∧
          Condition2 (obsSet δ ω) p (1 / (32 * condNum S)) X Y} ≤
        ENNReal.ofReal (Cfail / (n : ℝ) ^ 10) := by sorry

end NoisyMC.Convex
