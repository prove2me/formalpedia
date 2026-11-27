-- Prove2me | Theorems.Thm_MPBSelect_Supplement_theorem_9
-- name    : MPBSelect.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:52:00.521115+00:00
-- url     : https://prove2.me/theorems/671d2217-96b8-4e34-bf76-4aaa26b042e5
-- title:
--   Theorem 9 (corrected: invertible kernel matrix) — limiting CGF of the kernel-ridge predictive means
-- statement:
--   Fix one solution, a positive KRR penalty and a kernel whose matrix $K_i=(K(\theta_b,\theta_{b'}))$ is invertible. Suppose every sample count is positive, $N_i^n(\theta_b)/n\to\alpha_i(\theta_b)$ and $N_i^n(\theta_b)\to\infty$. Let the posterior means $\mu_{i,n}(\theta_b)$ of (5), under any normal prior, be independent across $\theta_b$ with the normal laws Model (4) gives them, and let $\widehat\mu_{i,n}$ be the kernel-ridge predictive means of (31) (Theorem 8). Then for every $t\in\mathbb R^B$,
--
--   $$
--   \lim_{n\to\infty}\frac1n\widehat\Lambda_{i,n}(nt)
--   =\sum_{b=1}^B\left(y_i(\theta_b)t_b+
--     \frac{\lambda_i^2(\theta_b)t_b^2}{2\alpha_i(\theta_b)}\right).
--   $$
--
--   When $\alpha_i(\theta_b)=0$, the right side is interpreted in the extended reals: its quadratic term is $+\infty$ for $t_b\ne0$ and zero for $t_b=0$. This retains the full domain allowed by the paper's sublinear-but-diverging counts.
--
--   Differences from the source:
--   - encoding: the real formula divides by $\alpha_i(\theta_b)$ although the standing allocation model permits zero ratios → an `EReal` limit with the standard $t_b^2/0=+\infty$ large-deviations convention and value zero when $t_b=0$; reason: this states (33) on the paper's full domain without silently adding positive allocation ratios
--   - encoding: $\log E\exp(t^\top\widehat\mu)$ → the logarithm of a nonnegative integral; reason: a divergent exponential moment becomes $+\infty$ rather than the Bochner integral's default zero
--   - correction: any positive-definite kernel in the sense of p.27 ($\sum K(\theta_\ell,\theta_{\ell'})c_\ell c_{\ell'}\ge0$) → the kernel matrix $K_i$ is invertible; reason: for a singular $K_i$ (e.g. $K\equiv0$, which is positive-definite in that sense) the predictive means are the constant $\beta_i\mathbf 1_B$, so the left side of (33) is $\beta_i\sum_bt_b$, not the printed limit when $y_i(\theta_b)\ne\beta_i$; the proof (p.ec31) uses $K_i(K_i+\kappa\Sigma_{i,n})^{-1}\to I$, which holds exactly when $K_i$ is invertible
--   - encoding: $\widehat\mu_{i,n}$ by the printed (32) with $\kappa\Sigma_{i,n}$ → the corrected closed form of (31) with $2\kappa\Sigma_{i,n}$ (Theorem 8); reason: this is the predictive mean the page defines, and since $\kappa>0$ is arbitrary the two formulas describe the same family of estimators
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Theorem 9 and (33), p.28; zero sampling ratios allowed in the standing allocation model, p.11

import Mathlib
import Definitions.Def_MPBSelect_Supplement_KRR

open Filter MeasureTheory
open scoped Topology

namespace MPBSelect.Supplement

/-- **Theorem 9 (limiting CGF of the kernel-ridge predictive means; corrected: invertible `K_i`).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 9,
p.28, equation (33).

If every count tends to infinity and `N_i^n(θ_b)/n → α_i(θ_b)`, the scaled CGF of the
closed-form KRR predictive means converges to the sum in (33). At `α_i(θ_b)=0`, the equation is
read in `EReal`: the quadratic term is `+∞` for `t_b ≠ 0` and zero for `t_b=0`.

**Formalization Note** (corrected: invertible `K_i`). The page's positive-definite kernels
(p.27: `Σ K(θ_ℓ,θ_ℓ')c_ℓc_ℓ' ≥ 0`) include kernels with a singular matrix `K_i`, e.g. `K ≡ 0`, for
which the predictive means are the constant `β_i 1_B` and (33) fails. The proof (p.ec31) uses
`K_i (K_i + κΣ_{i,n})⁻¹ → I`, which holds exactly when `K_i` is invertible; that hypothesis is
added. The predictive means are those of (31), i.e. the corrected closed form of Theorem 8
(`2κ Σ`); since `κ > 0` is arbitrary this is the same family of estimators as the printed (32).
The posterior means are those of (5) under an arbitrary normal prior. -/
theorem theorem_9 {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (feature : Fin B → H) (hK : (kernelMatrix feature).det ≠ 0) (β κ : ℝ) (hκ : 0 < κ)
    (N : ℕ → Fin B → ℕ) (α : Fin B → ℝ)
    (hNpos : ∀ n b, 0 < N n b)
    (hNratio : ∀ b, Tendsto (fun n : ℕ => (N n b : ℝ) / (n : ℝ)) atTop (𝓝 (α b)))
    (hNinf : ∀ b, Tendsto (fun n => N n b) atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Fin B → Ω → ℝ) (pr : GaussianPrior k B)
    (hX : IsGaussianMeanArray P i pr μ N X)
    (t : Fin B → ℝ) :
    Tendsto (fun n => scaledKernelCGF μ
      (fun m ω => krrClosedForm P i feature (N m) (fun b => X m b ω) β κ) n t)
      atTop (𝓝 (∑ b, cgfLimitTerm (P.y i b) (P.lam i b) (α b) (t b))) := by sorry

end MPBSelect.Supplement
