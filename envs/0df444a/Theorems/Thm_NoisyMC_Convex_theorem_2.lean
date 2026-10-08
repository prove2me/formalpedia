-- Prove2me | Theorems.Thm_NoisyMC_Convex_theorem_2
-- name    : NoisyMC.Convex.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:59.156454+00:00
-- url     : https://prove2.me/theorems/e6c86d11-648f-4995-b39f-c9f5fd3cab24
-- title:
--   Theorem 2 — every minimizer of the nuclear-norm regularized least squares (3) attains near-optimal Frobenius, entrywise and spectral errors, and is nearly rank r
-- statement:
--   Let $M^\star\in\mathbb R^{n\times n}$ have rank $r$, be $\mu$-incoherent (Definition 1), and have extreme singular values $\sigma_{\max},\sigma_{\min}$ and condition number $\kappa=\sigma_{\max}/\sigma_{\min}$. One observes $M_{ij}=M^\star_{ij}+E_{ij}$ for $(i,j)\in\Omega$, where Assumption 1 holds: each index enters $\Omega$ independently with probability $p$, and the noise entries are i.i.d., zero-mean, with sub-Gaussian norm at most $\sigma>0$. Take $\lambda=C_\lambda\sigma\sqrt{np}$ in
--
--   $$\operatorname*{minimize}_{Z\in\mathbb R^{n\times n}}\ \frac12\sum_{(i,j)\in\Omega}(Z_{ij}-M_{ij})^2+\lambda\|Z\|_*\qquad(3)$$
--
--   for a large enough constant $C_\lambda>0$. Assume $n^2p\ge C\kappa^4\mu^2r^2n\log^3n$ for a sufficiently large constant $C>0$ and $\sigma\sqrt{n/p}\le c\,\sigma_{\min}/\sqrt{\kappa^4\mu r\log n}$ for a sufficiently small constant $c>0$. Then with probability exceeding $1-O(n^{-3})$:
--
--   1. any minimizer $Z_{\rm cvx}$ of (3) obeys
--   $$\|Z_{\rm cvx}-M^\star\|_F\lesssim\kappa\frac\sigma{\sigma_{\min}}\sqrt{\frac np}\,\|M^\star\|_F,\qquad(11a)$$
--   $$\|Z_{\rm cvx}-M^\star\|_\infty\lesssim\sqrt{\kappa^3\mu r}\cdot\frac\sigma{\sigma_{\min}}\sqrt{\frac{n\log n}p}\,\|M^\star\|_\infty,\qquad(11b)$$
--   $$\|Z_{\rm cvx}-M^\star\|\lesssim\frac\sigma{\sigma_{\min}}\sqrt{\frac np}\,\|M^\star\|;\qquad(11c)$$
--   2. any best rank-$r$ approximation $Z_{{\rm cvx},r}$ of $Z_{\rm cvx}$ satisfies
--   $$\|Z_{{\rm cvx},r}-Z_{\rm cvx}\|_F\le\frac1{n^3}\cdot\frac\sigma{\sigma_{\min}}\sqrt{\frac np}\,\|M^\star\|,\qquad(12)$$
--   and the error bounds (11) continue to hold with $Z_{{\rm cvx},r}$ in place of $Z_{\rm cvx}$.
--
--   This is the paper's main result. Plain nuclear-norm regularized least squares, with no spikiness constraint, achieves errors that are minimax optimal up to logarithmic factors when $r,\kappa=O(1)$. It does so in the Frobenius norm, in the entrywise norm and in the spectral norm, and its solution is extremely close to rank $r$.
--
--   **Formalization Note.** Quantifiers: there is $C_{\lambda0}>0$ such that for every $C_\lambda\ge C_{\lambda0}$ there are $C,c,C_1,C_2,C_3,C_{\rm fail}>0$ and $n_0$ such that for every $n\ge n_0$ and all data (rank $r\ge1$, $\mu$, $M^\star$ with its SVD, $0<p\le1$, $\sigma>0$, probability space, sampling and noise satisfying Assumption 1, including the added independence of sampling and noise), the event "every minimizer $Z$ of (3) satisfies (11a)–(11c) with constants $C_1,C_2,C_3$, and every best rank-$r$ approximation $Z_r$ of $Z$ satisfies (12) and (11a)–(11c)" fails with outer probability at most $C_{\rm fail}n^{-3}$. "$\lesssim$" is Remark 2's: bounded by a constant times the right-hand side for $n$ large; the constant $1$ in (12) is the paper's. Program (3) is $g(Z)=\frac12\|\mathcal P_\Omega(Z-M)\|_F^2+\lambda\|Z\|_*$ with $M=M^\star+E$. $\|\cdot\|$ is the spectral norm, $\|\cdot\|_\infty$ the largest absolute entry, and $\log$ the natural logarithm. The noise condition of Remark 4 and the extension to approximate minimizers (Remark 6) are not part of this statement.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), pp. 8–9, Theorem 2, (11a)–(11c), (12); Assumption 1 and Definition 1, p. 5; Remark 2, p. 6

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Theorem 2 (pp. 8–9). There is `C_λ0 > 0` such that for every `C_λ ≥ C_λ0` there are constants
`C, c, C₁, C₂, C₃, C_fail > 0` and `n₀` with the following property. Let `n ≥ n₀`, let
`M⋆ ∈ ℝ^{n×n}` be rank `r ≥ 1` (SVD `S`; `σ_max, σ_min`, condition number `κ`) and
`µ`-incoherent, `0 < p ≤ 1`, `σ > 0`, and let the sampling pattern `Ω` and the noise `E` obey
Assumption 1. Take `λ = C_λ σ √(np)` in (3), and assume `n² p ≥ C κ⁴ µ² r² n log³ n` and
`σ √(n/p) ≤ c σ_min / √(κ⁴ µ r log n)`. Then with probability at least `1 − C_fail n^{-3}`:
1. every minimizer `Z_cvx` of (3) obeys
   (11a) `‖Z_cvx − M⋆‖_F ≤ C₁ κ (σ/σ_min) √(n/p) ‖M⋆‖_F`,
   (11b) `‖Z_cvx − M⋆‖_∞ ≤ C₂ √(κ³µr) (σ/σ_min) √(n log n / p) ‖M⋆‖_∞`,
   (11c) `‖Z_cvx − M⋆‖ ≤ C₃ (σ/σ_min) √(n/p) ‖M⋆‖`;
2. every best rank-`r` approximation `Z_cvx,r` of such a `Z_cvx` obeys
   (12) `‖Z_cvx,r − Z_cvx‖_F ≤ n^{-3} (σ/σ_min) √(n/p) ‖M⋆‖`,
   and (11a)–(11c) with `Z_cvx,r` in place of `Z_cvx`. -/
theorem theorem_2 :
    ∃ Clam0 : ℝ, 0 < Clam0 ∧ ∀ Clam : ℝ, Clam0 ≤ Clam →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ C₃ : ℝ, 0 < C₃ ∧ ∃ Cfail : ℝ, 0 < Cfail ∧
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
      let errorBounds : RealMatrix n n → Prop := fun W =>
        frobeniusNorm (W - Mstar) ≤
            C₁ * condNum S * (σ / sigmaMin S) * Real.sqrt (n / p) * frobeniusNorm Mstar ∧
          entrySupNorm (W - Mstar) ≤
            C₂ * Real.sqrt (condNum S ^ 3 * μ * r) * (σ / sigmaMin S) *
              Real.sqrt (n * Real.log n / p) * entrySupNorm Mstar ∧
          spectralNorm (W - Mstar) ≤
            C₃ * (σ / sigmaMin S) * Real.sqrt (n / p) * spectralNorm Mstar
      P {ω | ¬ ∀ Z : RealMatrix n n, IsCvxMinimizer (obsSet δ ω) (dataMatrix Mstar E ω) lam Z →
          errorBounds Z ∧
          ∀ Zr : RealMatrix n n, IsBestRankApprox r Z Zr →
            frobeniusNorm (Zr - Z) ≤
              1 / (n : ℝ) ^ 3 * (σ / sigmaMin S) * Real.sqrt (n / p) * spectralNorm Mstar ∧
            errorBounds Zr} ≤
        ENNReal.ofReal (Cfail / (n : ℝ) ^ 3) := by sorry

end NoisyMC.Convex
