-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_mle_consistent
-- name    : McFadden1974.Asymptotics.mle_consistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:19.678829+00:00
-- url     : https://prove2.me/theorems/3af1eeff-54e4-456f-ad36-7147af8ba4e7
-- title:
--   Lemma 6, consistency — the conditional logit maximum likelihood estimator is consistent
-- statement:
--   Let the choices be independent drawings from the conditional logit probabilities at the true parameter $\theta^0$ (Axioms 1–4), let the data satisfy Axiom 7, and let $\hat\theta^q$ be a maximum likelihood estimator for the first $q$ observations: a measurable selection that maximizes $L^q$ whenever a maximizer exists. Then $\hat\theta^q$ is consistent:
--   $$\hat\theta^q \xrightarrow{\ \Pr\ } \theta^0 \qquad (q\to\infty),$$
--   i.e. $\Pr(|\hat\theta^q - \theta^0| > \varepsilon) \to 0$ for every $\varepsilon > 0$.
--
--   This is the first half of Lemma 6 and the starting point of the asymptotic normality argument.
--
--   **Formalization Note** Nothing is assumed about $\hat\theta^q$ where no maximizer exists; by Lemma 5 that event has probability tending to zero. Measurability of $\hat\theta^q$ is an assumption on the estimator.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 135, Lemma 6 (consistency), proof pp. 135–137, Equations (49)–(53); PDF pp. 31–33

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Consistency of the maximum likelihood estimator** (Lemma 6, first assertion and proof,
pp. 135–137, PDF pp. 31–33: "We shall first establish that θ̂^m is a consistent estimator of θ⁰
… Since this event occurs with probability at least 1 − ε, we have proved the estimator to be
consistent."): under Axioms 1–4 and 7, with `θ⁰` the true parameter vector, `θ̂^q → θ⁰` in
probability as the sample size `q` tends to infinity.

Formalization Note: Axioms 1–4 are the sampling model `IsLogitSample` at `θ⁰`; Axiom 7 is
`Axiom7` in the serial form (48). `θ̂^q` is any measurable selection that maximizes the
log-likelihood of the first `q` observations whenever a maximizer exists (`IsMLE`); nothing is
asserted about its values where no maximizer exists. Consistency is convergence in measure
(`TendstoInMeasure`) to the constant `θ⁰` in the Euclidean distance. -/
theorem mle_consistent {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin K))
    (hθ : IsMLE D Y θhat) :
    TendstoInMeasure μ θhat atTop (fun _ => θ₀) := by sorry

end McFadden1974.Asymptotics
