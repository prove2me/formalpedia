-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_score_clt
-- name    : McFadden1974.Asymptotics.score_clt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:23.147502+00:00
-- url     : https://prove2.me/theorems/b3d348fc-744f-49d6-a97b-97d94ba71bcd
-- title:
--   Equation (58) — the normalized score $q^{-1/2}\Omega^{-1/2}L^q_\theta(\theta^0)$ is asymptotically standard normal
-- statement:
--   Under the sampling model at the true parameter $\theta^0$ and Axiom 7, let $\lambda^m_\theta(\theta^0) = \nabla_\theta \log P_{Y_m m}(\theta^0)$ be the score of observation $m$, and $\Omega^{-1/2}$ the inverse of the positive semidefinite square root of the limit matrix $\Omega$. Then
--   $$\frac{1}{\sqrt q}\,\Omega^{-1/2} L^q_\theta(\theta^0) = \frac{1}{\sqrt q} \sum_{m<q} \Omega^{-1/2}\lambda^m_\theta(\theta^0) \ \xrightarrow{\ d\ }\ N(0, I_K) \qquad (q\to\infty).$$
--
--   The summands are independent and bounded but not identically distributed; this is the central limit step that, combined with consistency and the Taylor expansion of the score, yields Lemma 6.
--
--   **Formalization Note** The paper prints the normalization as $1/q$, a misprint for $1/\sqrt q$ (with $1/q$ the limit is $0$). Convergence in distribution is to a random vector with the standard Gaussian law on $\mathbb R^K$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), pp. 137–138, Equation (58) and the sentence after it (Lemma 6, proof); PDF pp. 33–34

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Equation (58), the central limit step** (Lemma 6, proof, pp. 137–138, PDF pp. 33–34):
"(58) (1/q) Ω^{−1/2} L_θ^q(θ⁰) = (1/q) Σ_{m=1}^{q} Ω^{−1/2} λ_θ^m(θ⁰). But the independent random
variables Ω^{−1/2}λ_θ^m(θ⁰) satisfy the Lindeberg–Levy theorem (Feller, 1966, Vol. II,
pp. 256–258), implying that Equation (58) is asymptotic standard normal."

Formalization Note: the normalization printed `1/q` in (58) is a misprint for `1/√q`: with
`1/q` the sum tends to `0` in probability, and the asymptotic standard normality the paper asserts
(and uses for `√q Ω^{1/2}(θ̂^q − θ⁰)`) holds for `(1/√q) Σ_{m<q} Ω^{−1/2} λ_θ^m(θ⁰)`. The scores
`λ_θ^m(θ⁰) = ∇_θ log P_{Y_m m}(θ⁰)` are independent but not identically distributed (their
covariances are the `Ω_m` of (47)); "Lindeberg–Levy" here is the Lindeberg–Feller theorem.
Convergence in distribution is `TendstoInDistribution` to a random vector `Z` on an auxiliary
probability space whose law is the standard Gaussian measure on `ℝ^K`. `Ω^{−1/2}` is
`invSqrtMap Ω`. -/
theorem score_clt {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (Z : Ω' → EuclideanSpace ℝ (Fin K)) (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin K))) μ') :
    TendstoInDistribution
      (fun (q : ℕ) (ω : Ω) => (Real.sqrt q)⁻¹ • ∑ m ∈ Finset.range q,
        invSqrtMap Ωlim (gradient (fun θ => Real.log (prob D m (Y m ω) θ)) θ₀))
      atTop Z (fun _ => μ) μ' := by sorry

end McFadden1974.Asymptotics
