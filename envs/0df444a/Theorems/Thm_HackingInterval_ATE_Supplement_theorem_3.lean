-- Prove2me | Theorems.Thm_HackingInterval_ATE_Supplement_theorem_3
-- name    : HackingInterval.ATE.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:56:47.498771+00:00
-- url     : https://prove2.me/theorems/ee39e23c-2ed8-42cc-98ff-a41de4ae2478
-- title:
--   Theorem 3 — both Gaussian ATE endpoint variances with the exact Gamma constant
-- statement:
--   Fix arbitrary treatment covariates and assignments with full design $\widetilde X=[X,1[\mathrm{treated}]]$, $n$ observations, and $p$ confounders. Assume $\widetilde X^\top\widetilde X$ is invertible and $\nu=n-p-1>0$. For every true coefficient vector $\beta\in\mathbb R^{p+1}$, every noise standard deviation $\sigma\ge0$, and every $r>0$, sample $Y$ under Equation (19),
--
--   $$Y\sim N(\widetilde X\beta,\sigma^2 I).$$
--
--   For each realization use the same $Y$ to compute $s(Y)=\mathrm{SSE}(Y)$ and the threshold $\theta(Y)=(1+r)s(Y)$. Write $B_-(Y)$ and $B_+(Y)$ for the resulting treatment hacking bounds. Both variables have finite second moments and
--
--   $$\operatorname{Var}(B_-\mid\widetilde X)=\operatorname{Var}(B_+\mid\widetilde X)=\sigma^2 V_{tt}\left(1+r(\nu-\mu_\nu^2)\right),\qquad\mu_\nu=\sqrt2\frac{\Gamma((\nu+1)/2)}{\Gamma(\nu/2)}.$$
--
--   This gives the exact sampling variance of both bounds for every permitted design and every tolerance ratio. The design is fixed and arbitrary, so the variances are taken only over outcomes. Zero noise remains included. No derived coefficient distribution, residual distribution, or fitted-residual independence is assumed.
--
--   Differences from the source:
--   - encoding: Equation (19) gives a multivariate Gaussian response conditional on the fixed full design → the measure is the product of coordinate Gaussians with means X̃β and common variance σ²; reason: this is exactly N(X̃β,σ²I); fixing the design expresses conditioning, and σ is a nonnegative standard deviation including zero
--   - encoding: inverse matrices and the Gamma ratio require their mathematical domains → the full Gram determinant is a unit and p+1<n; reason: the positive integer ν=n−p−1 gives positive Gamma arguments and excludes only undefined source expressions
--   - encoding: SSE and both endpoint bounds are evaluated on the random outcomes → withResponse replaces Y pointwise and θ(Y)=(1+r)SSE(Y); reason: the threshold is not frozen independently of the response; the published full-design SSE is reused
--   - encoding: the source states finite real variances of both bounds → both MemLp second-moment conclusions accompany the two Mathlib variance equalities; reason: finite moments are proved conclusions, preventing default variance values from masking nonintegrability
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), DOI 10.1287/mnsc.2020.3818, p. 12 (PDF 13), Theorem 3, eqs. (19)–(21); published Online Appendix D ec17

import Mathlib
import Definitions.Def_HackingInterval_ATE_Supplement_Calibration
import Definitions.Def_HackingInterval_ATE_Supplement_GaussianEndpoints
import Definitions.Def_HackingInterval_ATE_Supplement_ChiMean
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal

namespace HackingInterval.ATE.Supplement

/-- Theorem 3, both conditional variances under Equation (19).
The design is fixed and arbitrary; only Y is sampled. No derived Gaussian/chi law is assumed. -/
theorem theorem_3 {n p : ℕ} (D : TreatData n p)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hdof : p + 1 < n)
    (β : Fin p ⊕ Unit → ℝ) (σ : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    let P := responseLaw D β σ
    let ν := residualDof n p
    let v := (σ : ℝ) ^ 2 * D.Vtt * (1 + r * ((ν : ℝ) - chiMean ν ^ 2))
    MemLp (lowerEndpoint D r) 2 P ∧ MemLp (upperEndpoint D r) 2 P ∧
      variance (lowerEndpoint D r) P = v ∧ variance (upperEndpoint D r) P = v := by sorry

end HackingInterval.ATE.Supplement
