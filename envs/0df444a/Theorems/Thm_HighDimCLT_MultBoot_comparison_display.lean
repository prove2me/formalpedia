-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_comparison_display
-- name    : HighDimCLT.MultBoot.comparison_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:29.665991+00:00
-- url     : https://prove2.me/theorems/62e17d54-d868-4ff4-9be9-d2fdf97ca275
-- title:
--   App. E.2, p. 2342 — |E[g(F_β(S^{eX}_n)) | X₁ⁿ] − E[g(F_β(S^Y_n))]| ≤ (‖g″‖_∞/2 + β‖g′‖_∞)Δ_{n,r}
-- statement:
--   Assume the standing setting with $n\ge4$, $p\ge3$: $X_1,\dots,X_n$ independent centred square-integrable random vectors in $\mathbb R^p$, and $Y_1,\dots,Y_n$ independent with $Y_i\sim N(0,\mathrm E[X_iX_i'])$. Fix a realization $x$ of the data, $\beta>0$, $y\in\mathbb R^p$, and a twice continuously differentiable $g:\mathbb R\to\mathbb R$ with $|g'|\le G_1$ and $|g''|\le G_2$ everywhere. Then
--   $$\Big|\mathrm E\big[g(F_\beta(S_n^{eX}))\mid X_1^n=x\big]-\mathrm E\big[g(F_\beta(S_n^Y))\big]\Big|\le\Big(\frac{G_2}{2}+\beta G_1\Big)\Delta_{n,r},$$
--   where $F_\beta$ is the smooth max centred at $y$ and $\Delta_{n,r}=\max_{j,k}|\widehat\Sigma_{jk}-\Sigma_{jk}|$ is computed from $x$.
--
--   This is a Gaussian-to-Gaussian comparison: it bounds the effect of replacing the covariance $\Sigma$ of $S^Y_n$ by the bootstrap covariance $\widehat\Sigma$ on smooth functionals of the maximum.
--
--   **Formalization Note** The page writes the bound with the sup norms $\|g'\|_\infty,\|g''\|_\infty$; quantifying over all bounds $G_1,G_2$ is equivalent. The conditional expectation is the integral against the bootstrap law at the realization $x$; the statement is made for every $x$, hence for every realization. Both integrands are continuous with at most linear growth, hence integrable under Gaussian laws, so neither integral takes a default value.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2342, App. E.2, Proof of Theorem 4.1, display after "a small modification of the proof of Theorem 1 in [20]"

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Gaussian comparison display**, App. E.2, p. 2342: for every `g ∈ C²(ℝ)` with
`|g′| ≤ G₁` and `|g″| ≤ G₂` everywhere and every `β > 0`, `y ∈ ℝ^p`,
`|E[g(F_β(S^{eX}_n)) | X₁ⁿ = x] − E[g(F_β(S^Y_n))]| ≤ (G₂/2 + β G₁) Δ_{n,r}`, where the
conditional expectation is the integral against the bootstrap law `mbLaw x` and
`Δ_{n,r} = max_{j,k} |Σ̂_jk − Σ_jk|` is computed from the realization `x`. -/
theorem comparison_display {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n p : ℕ) (hn : 4 ≤ n) (hp : 3 ≤ p)
    (X Y : Fin n → Ω → EuclideanSpace ℝ (Fin p)) (hS : Standing P X Y)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (β : ℝ) (hβ : 0 < β) (y : EuclideanSpace ℝ (Fin p))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (G₁ G₂ : ℝ) (hG₁ : ∀ t, |deriv g t| ≤ G₁)
    (hG₂ : ∀ t, |deriv (deriv g) t| ≤ G₂) :
    |∫ w, g (Fβ β y w) ∂(mbLaw x) - ∫ ω, g (Fβ β y (normSum Y ω)) ∂P|
      ≤ (G₂ / 2 + β * G₁) * DeltaR x P X := by sorry

end HighDimCLT.MultBoot
