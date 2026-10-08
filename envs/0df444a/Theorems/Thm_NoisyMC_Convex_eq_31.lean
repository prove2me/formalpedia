-- Prove2me | Theorems.Thm_NoisyMC_Convex_eq_31
-- name    : NoisyMC.Convex.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:03.140998+00:00
-- url     : https://prove2.me/theorems/c78a03b8-ac86-4b5f-8afc-edca393595bb
-- title:
--   (31a)–(31c) — the bounds (29) on (XH, YH) give ‖XYᵀ − M⋆‖ in F, ℓ∞ and operator norm with factors 3κC_F, 3C_∞√(κ³µr), 3C_op
-- statement:
--   Let $M^\star\in\mathbb R^{n\times n}$ be rank $r\ge1$ and $\mu$-incoherent, with extreme singular values $\sigma_{\max},\sigma_{\min}$, condition number $\kappa$ and balanced factors $X^\star,Y^\star$. Let $0<p\le1$, $\sigma>0$ and $\lambda=C_\lambda\sigma\sqrt{np}$, and assume the noise is small: $\frac\sigma{\sigma_{\min}}\sqrt{\frac np}\le\frac c{\sqrt{\kappa^2\log n}}$ for a sufficiently small constant $c>0$. Let $X,Y\in\mathbb R^{n\times r}$ and let $H$ be orthogonal such that $(XH,YH)$ satisfies (29a)–(29c) of Lemma 5 with constants $C_F,C_{\rm op},C_\infty$. Then
--
--   $$\|XY^\top-M^\star\|_F\le3\kappa C_F\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac np}+\frac\lambda{p\sigma_{\min}}\Big)\|M^\star\|_F,\qquad(31a)$$
--
--   $$\|XY^\top-M^\star\|_\infty\le3C_\infty\sqrt{\kappa^3\mu r}\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac{n\log n}p}+\frac\lambda{p\sigma_{\min}}\Big)\|M^\star\|_\infty,\qquad(31b)$$
--
--   $$\|XY^\top-M^\star\|\le3C_{\rm op}\Big(\frac\sigma{\sigma_{\min}}\sqrt{\frac np}+\frac\lambda{p\sigma_{\min}}\Big)\|M^\star\|.\qquad(31c)$$
--
--   Applied to the iterates of Algorithm 1 on the event of Lemma 5, this gives the paper's (31) for all $0\le t\le t_0$. These bounds are what Theorem 2 transfers to the convex estimator.
--
--   **Formalization Note.** The paper states (31) "with high probability" as an immediate consequence of Lemma 5; its proof (App. D.12) is deterministic given (29a)–(29c) at one $t$, the noise bound above (used to get $\|Y H\|\le2\|X^\star\|$ and $\|YH\|_{2,\infty}\le2\max\{\|X^\star\|_{2,\infty},\|Y^\star\|_{2,\infty}\}$), and incoherence. It is stated in that deterministic form: for all $C_F,C_{\rm op},C_\infty,C_\lambda>0$ there are $c>0$ and $n_0$. The factors $3\kappa C_F$, $3C_\infty\sqrt{\kappa^3\mu r}$ and $3C_{\rm op}$ are the paper's. $\|\cdot\|_\infty$ is the largest absolute entry.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 14, (31a)–(31c); proof App. D.12, pp. 61–62

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- (31a)–(31c) (§2.5, p. 14; proof in App. D.12, pp. 61–62), in the deterministic form of the
proof. For all constants `C_F, C_op, C_∞, C_λ > 0` there are `c > 0` and `n₀` such that for every
`n ≥ n₀`, every rank-`r` `µ`-incoherent `M⋆` (SVD `S`, factors `X⋆, Y⋆`, `σ_max, σ_min, κ`),
every `0 < p ≤ 1`, `σ > 0` with the noise bound `(σ/σ_min) √(n/p) ≤ c / √(κ² log n)`, with
`λ = C_λ σ √(np)`, and every `X, Y ∈ ℝ^{n×r}` and orthogonal `H` such that `(XH, YH)` obeys the
bounds (29a)–(29c) of Lemma 5 with constants `C_F, C_op, C_∞`:
(31a) `‖X Yᵀ − M⋆‖_F ≤ 3κ C_F ((σ/σ_min)√(n/p) + λ/(pσ_min)) ‖M⋆‖_F`,
(31b) `‖X Yᵀ − M⋆‖_∞ ≤ 3 C_∞ √(κ³µr) ((σ/σ_min)√(n log n/p) + λ/(pσ_min)) ‖M⋆‖_∞`,
(31c) `‖X Yᵀ − M⋆‖ ≤ 3 C_op ((σ/σ_min)√(n/p) + λ/(pσ_min)) ‖M⋆‖`. -/
theorem eq_31 :
    ∀ CF : ℝ, 0 < CF → ∀ Cop : ℝ, 0 < Cop → ∀ Cinf : ℝ, 0 < Cinf → ∀ Clam : ℝ, 0 < Clam →
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ r : ℕ, 1 ≤ r →
    ∀ (μ : ℝ) (Mstar : RealMatrix n n) (S : SVD Mstar r), A0 S μ →
    ∀ (p σ : ℝ), 0 < p → p ≤ 1 → 0 < σ →
      σ / sigmaMin S * Real.sqrt (n / p) ≤ c / Real.sqrt (condNum S ^ 2 * Real.log n) →
    let lam : ℝ := Clam * σ * Real.sqrt (n * p)
    ∀ (X Y : RealMatrix n r) (H : Matrix (Fin r) (Fin r) ℝ),
      H ∈ Matrix.orthogonalGroup (Fin r) ℝ →
      max (frobeniusNorm (X * H - Xstar S)) (frobeniusNorm (Y * H - Ystar S)) ≤
        CF * (σ / sigmaMin S * Real.sqrt (n / p) + lam / (p * sigmaMin S)) *
          frobeniusNorm (Xstar S) →
      max (spectralNorm (X * H - Xstar S)) (spectralNorm (Y * H - Ystar S)) ≤
        Cop * (σ / sigmaMin S * Real.sqrt (n / p) + lam / (p * sigmaMin S)) *
          spectralNorm (Xstar S) →
      max (twoInfNorm (X * H - Xstar S)) (twoInfNorm (Y * H - Ystar S)) ≤
        Cinf * condNum S *
          (σ / sigmaMin S * Real.sqrt (n * Real.log n / p) + lam / (p * sigmaMin S)) *
          max (twoInfNorm (Xstar S)) (twoInfNorm (Ystar S)) →
      frobeniusNorm (X * Y.transpose - Mstar) ≤
          3 * condNum S * CF * (σ / sigmaMin S * Real.sqrt (n / p) + lam / (p * sigmaMin S)) *
            frobeniusNorm Mstar ∧
        entrySupNorm (X * Y.transpose - Mstar) ≤
          3 * Cinf * Real.sqrt (condNum S ^ 3 * μ * r) *
            (σ / sigmaMin S * Real.sqrt (n * Real.log n / p) + lam / (p * sigmaMin S)) *
            entrySupNorm Mstar ∧
        spectralNorm (X * Y.transpose - Mstar) ≤
          3 * Cop * (σ / sigmaMin S * Real.sqrt (n / p) + lam / (p * sigmaMin S)) *
            spectralNorm Mstar := by sorry

end NoisyMC.Convex
