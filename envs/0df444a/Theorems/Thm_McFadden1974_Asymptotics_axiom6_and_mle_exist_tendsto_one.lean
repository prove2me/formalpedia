-- Prove2me | Theorems.Thm_McFadden1974_Asymptotics_axiom6_and_mle_exist_tendsto_one
-- name    : McFadden1974.Asymptotics.axiom6_and_mle_exist_tendsto_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:48:02.343349+00:00
-- url     : https://prove2.me/theorems/2a09b91d-634e-4082-9f2e-b111dd21e688
-- title:
--   Lemma 5 — Axiom 6 holds and the maximum likelihood estimator exists with probability tending to one
-- statement:
--   Let the choices $Y_0, Y_1, \dots$ be independent, with $Y_m$ drawn from the conditional logit probabilities $P_{im}(\theta^0)$ of Equation (16) at a true parameter $\theta^0\in\mathbb R^K$ (Axioms 1–4), and let the data satisfy Axiom 7 with limit matrix $\Omega$ positive definite. Let $A_q$ be the event that **Axiom 6** holds for the first $q$ observations, i.e. no nonzero $\gamma$ satisfies $(z_{jm}-z_{Y_m m})\gamma \le 0$ for all $m<q$ and all $j$, and that the log-likelihood $L^q$ attains its maximum. Then
--   $$\lim_{q\to\infty} \Pr(A_q) = 1 .$$
--
--   In a finite sample the maximum likelihood estimator can fail to exist with positive probability; this lemma shows that the failure is asymptotically negligible, which is what makes the asymptotic theory of Lemma 6 meaningful.
--
--   **Formalization Note** The sample size $\sum_n R_n$ is the number $q$ of serially indexed observations. The p. 120 statement, which includes "that Axiom 6 holds and", is formalized; the Appendix restatement (p. 134) omits that clause.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 120, Lemma 5 (restated with proof p. 134); PDF pp. 16, 30

import Mathlib
import Definitions.Def_McFadden1974_Asymptotics_LogitSample

namespace McFadden1974.Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Lemma 5** (p. 120, PDF p. 16; restated with proof p. 134, PDF p. 30): "Suppose Axioms 1–4
and 7 hold. Then the probability that Axiom 6 holds and the maximum likelihood estimator exists
approaches unity as Σ_{n=1}^N R_n approaches infinity."

Formalization Note: Axioms 1–4 are built into the model: the choices are drawn from the
conditional logit probabilities (16) at a true parameter `θ⁰` (`IsLogitSample`), independently
across observations. Axiom 7 is `Axiom7` in the serial form (48) with `Ω` evaluated at `θ⁰`.
The sample size `Σ R_n` is the number `q` of serially indexed observations. "The maximum
likelihood estimator exists" is: the log-likelihood `L^q(·, ω)` of the first `q` observations
attains its maximum. The p. 120 statement (with "that Axiom 6 holds and") is formalized; the
Appendix restatement on p. 134 omits that clause and is implied by it. The probability is the
outer measure of the event, which is in fact measurable. -/
theorem axiom6_and_mle_exist_tendsto_one {K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : SerialData K) (Jstar : ℕ) (M : ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin K)) (Ωlim : Matrix (Fin K) (Fin K) ℝ)
    (h7 : Axiom7 D Jstar M θ₀ Ωlim) (Y : (m : ℕ) → Ω → Fin (D.J m))
    (hY : IsLogitSample μ D θ₀ Y) :
    Tendsto (fun q : ℕ => μ {ω | Axiom6 D Y q ω ∧
        ∃ θ, ∀ θ', logLik D Y q θ' ω ≤ logLik D Y q θ ω}) atTop (𝓝 1) := by sorry

end McFadden1974.Asymptotics
