-- Prove2me | Theorems.Thm_OptimalRLS_Upper_theorem_1
-- name    : OptimalRLS.Upper.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:26:30.544658+00:00
-- url     : https://prove2.me/theorems/6b017f5a-7aa8-45c7-b3e1-7f9f31b87d21
-- title:
--   Theorem 1 (1 < b < +∞), p. 11 — with λ_ℓ of (19), RLS has upper rate a_ℓ of (20) uniformly over P(b, c)
-- statement:
--   Assume Hypothesis 1 with constant $\kappa$, fix positive constants $M,\Sigma,R,\alpha,\beta$, and let $1<b<+\infty$ and $1\le c\le2$. Let
--   $$\lambda_\ell=\begin{cases}(1/\ell)^{\frac b{bc+1}}&c>1\\[2pt](\log\ell/\ell)^{\frac b{b+1}}&c=1\end{cases}\qquad a_\ell=\begin{cases}(1/\ell)^{\frac{bc}{bc+1}}&c>1\\[2pt](\log\ell/\ell)^{\frac b{b+1}}&c=1,\end{cases}$$
--   and let $f_{\mathbf z}^{\lambda_\ell}$ be the regularized least-squares estimator (18) with parameter $\lambda_\ell$. Then
--   $$\lim_{\tau\to\infty}\limsup_{\ell\to\infty}\sup_{\rho\in\mathcal P(b,c)}\mathbb P_{\mathbf z\sim\rho^\ell}\Big[\mathcal E[f_{\mathbf z}^{\lambda_\ell}]-\mathcal E[f_{\mathcal H}]>\tau a_\ell\Big]=0.\tag{21}$$
--   That is: for every $\varepsilon>0$ there is $\tau_0$ such that for every $\tau\ge\tau_0$ there is $L$ with
--   $$\rho^\ell\Big[\mathcal E[f_{\mathbf z}^{\lambda_\ell}]-\inf_{f\in\mathcal H}\mathcal E[f]>\tau a_\ell\Big]\le\varepsilon\qquad\text{for all }\ell\ge L\text{ and all }\rho\in\mathcal P(b,c).$$
--
--   The rate $a_\ell$ holds uniformly over the prior $\mathcal P(b,c)$, which is determined by the decay $n^{-b}$ of the eigenvalues of $T$ and the source condition of order $c$. Theorems 2 and 3 of the paper show that this rate is minimax optimal for $1<c\le2$ when $Y$ is finite dimensional.
--
--   **Formalization Note** Only the branches $1<b<+\infty$ are stated. The paper also states a branch $b=+\infty$ with $\lambda_\ell=\ell^{-1/2}$ and $a_\ell=1/\ell$; it fails for $1\le c<2$: with $X=\{x_0,x_1\}$, $\mathcal H$ one-dimensional spanned by $\mathbf 1_{\{x_0\}}$, noiseless outputs and $\rho_X(x_0)=\ell^{-1/2}$, the excess risk stays of order $R\ell^{-c/2}/9\gg\tau/\ell$ with probability tending to $1$, so it is not posed. The $\lim\limsup\sup$ form is unfolded into the equivalent quantifier form above: probabilities lie in $[0,1]$ and the event shrinks as $\tau$ grows. $L$ is chosen before $\rho$, so the rate is uniform over $\mathcal P(b,c)$, and the estimator is fixed before $\rho$. The estimator is any family of maps `est ℓ` with `est ℓ z` a minimizer of (18) for $\lambda=\lambda_\ell$ and $\ell\ge2$; the minimizer is unique by Proposition 1 v). The requirement is dropped at $\ell=1$, where $\lambda_1=\log1=0$ when $c=1$ and (18) may have no minimizer; the conclusion only concerns large $\ell$. $\mathcal E[f_{\mathcal H}]$ is written as $\inf_{f\in\mathcal H}\mathcal E[f]$ by (8). The membership $\rho\in\mathcal P(b,c)$ includes Hypothesis 2, so the risk is a genuine integral. Events are measured by the outer product measure.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Theorem 1, (19)–(21), p. 11; Definition 1, pp. 9–10; proof §5.2, pp. 13–20

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Theorem 1** (p. 11), branches `1 < b < +∞`. With `λ_ℓ` of (19) and `a_ℓ` of (20), any
algorithm `est` returning the RLS estimator `f_z^{λ_ℓ}` (for `ℓ ≥ 2`) satisfies (21):
`lim_{τ→∞} limsup_{ℓ→∞} sup_{ρ∈P(b,c)} P_{z∼ρ^ℓ}[E[f_z^{λ_ℓ}] − E[f_H] > τ a_ℓ] = 0`, unfolded as
"for every `ε > 0` there is `τ₀` such that for every `τ ≥ τ₀` there is `L` with the probability
`≤ ε` for all `ℓ ≥ L` and all `ρ ∈ P(b, c)`". `E[f_H] = inf_{f∈H} E[f]` by (8). -/
theorem theorem_1
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig R α β : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (b c : ℝ) (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (est : (ℓ : ℕ) → (Fin ℓ → X × Y) → H)
    (hest : ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ z : Fin ℓ → X × Y, IsRLSMin (lamSeq b c ℓ) z (est ℓ z)) :
    ∀ ε : ℝ, 0 < ε → ∃ τ₀ : ℝ, ∀ τ : ℝ, τ₀ ≤ τ → ∃ L : ℕ, ∀ ℓ : ℕ, L ≤ ℓ →
      ∀ (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ], InPrior H M Sig R α β b c ρ →
        (Measure.pi fun _ : Fin ℓ => ρ)
            {z | τ * aSeq b c ℓ < risk ρ (est ℓ z) - ⨅ f : H, risk ρ f} ≤ ENNReal.ofReal ε := by sorry

end OptimalRLS.Upper
