-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_mle_consistent_asymptotically_normal
-- name    : McFadden1974.Asymptotics.mle_consistent_asymptotically_normal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:32.433198+00:00
-- url     : https://prove2.me/theorems/65b64d64-6c3c-485c-8e30-ff91f61766e6
-- title:
--   Lemma 6 — the conditional logit MLE is consistent and $\sqrt q\,\Omega^{1/2}(\hat\theta^q-\theta^0)$ is asymptotically standard normal
-- statement:
--   Let the choices $Y_0, Y_1, \dots$ be independent, with $Y_m$ drawn from the conditional logit probabilities (16) at the true parameter vector $\theta^0 \in \mathbb R^K$ (Axioms 1–4). Suppose **Axiom 7**: the numbers of alternatives are bounded by $J_*$, the independent variables by $M$, and the averaged moment matrices $\frac1q\sum_{m<q}\Omega_m(\theta^0)$ converge to a positive definite matrix $\Omega$. Let $\hat\theta^q$ be the maximum likelihood estimator for a sample of size $q$. Then
--
--   1. $\hat\theta^q$ is consistent: $\hat\theta^q \to \theta^0$ in probability;
--   2. $\hat\theta^q$ is asymptotically normal:
--   $$\sqrt q\;\Omega^{1/2}\bigl(\hat\theta^q - \theta^0\bigr) \ \xrightarrow{\ d\ }\ N(0, I_K) \qquad (q\to\infty).$$
--
--   Equivalently, $\hat\theta^q$ is approximately normal with mean $\theta^0$ and covariance $q^{-1}\Omega^{-1}$, which justifies the large-sample confidence bounds and $\chi^2$ tests on $\theta^0$ described after the lemma.
--
--   **Formalization Note** The paper's sample size $\sum_n R_n$ is the number $q$ of serially indexed observations. The maximum likelihood estimator is any measurable selection that maximizes the log-likelihood whenever a maximizer exists; by Lemma 5 this happens with probability tending to one. $\Omega^{1/2}$ is the positive semidefinite square root. The limit is a random vector with the standard Gaussian law on $\mathbb R^K$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 135, Lemma 6 (first stated p. 120, Lemma 6 with Equation (28)); PDF pp. 31, 16

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Lemma 6** (p. 135, PDF p. 31; first stated p. 120, PDF p. 16, with Equation (28)):
"Suppose Axioms 1–4 and 7 hold, θ⁰ is the true parameter vector and θ̂^m is the maximum likelihood
estimator for a sample of size m = Σ_{n=1}^N R_n. Then θ̂^m is consistent and asymptotically
normal as m → +∞, with √m Ω^{1/2}(θ̂^m − θ⁰), tending to a multivariate normal distribution with
mean zero and identity covariance matrix."

Formalization Note: Axioms 1–4 are the sampling model `IsLogitSample` (independent choices
drawn from the conditional logit probabilities (16) at `θ⁰`); Axiom 7 is `Axiom7`, with the
limit (27) in its serial form (48) and `Ω` evaluated at `θ⁰`, positive definite. The sample
size is the number `q` of serially indexed observations. `θ̂^q` is any measurable selection that
maximizes the log-likelihood whenever a maximizer exists (`IsMLE`); by Lemma 5 a maximizer
exists with probability tending to one. Consistency is convergence in probability to `θ⁰`;
asymptotic normality is convergence in distribution of `√q Ω^{1/2}(θ̂^q − θ⁰)` to a random vector
`Z` whose law is the standard Gaussian measure on `ℝ^K`, with `Ω^{1/2}` the positive
semidefinite square root (`sqrtMap`). -/
theorem mle_consistent_asymptotically_normal {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hθ : IsMLE D Y θhat)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Z : Ω' → EuclideanSpace ℝ (Fin K)) (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin K))) μ') :
    TendstoInMeasure μ θhat atTop (fun _ => θ₀) ∧
      TendstoInDistribution
        (fun (q : ℕ) (ω : Ω) => Real.sqrt q • sqrtMap Ωlim (θhat q ω - θ₀))
        atTop Z (fun _ => μ) μ' := by sorry

end McFadden1974.Asymptotics
