-- Prove2me | Theorems.Thm_FuchsThesis_Chernoff_eq_2_9
-- name    : FuchsThesis.Chernoff.eq_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:01.419515+00:00
-- url     : https://prove2.me/theorems/b77423f7-8066-4142-b7f7-2053ce73ae04
-- title:
--   Eq. (2.9) — Bayes' decision function minimizes the error probability
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite outcome set and let $\pi_0, \pi_1 \ge 0$ be priors with $\pi_0 + \pi_1 = 1$. Let $\delta_B$ be any Bayes decision function (any tie-breaking) and $\delta$ any decision function. Then
--
--   $$
--   P_e(\delta_B) \le P_e(\delta),
--   $$
--
--   and if $\delta$ is not a Bayes decision function, that is, $\delta$ disagrees with the Bayes choice at some outcome $b$ with $\pi_0 p_0(b) \neq \pi_1 p_1(b)$, then
--
--   $$
--   P_e(\delta) > P_e(\delta_B).
--   $$
--
--   This makes the Bayes error the best achievable probability of error for one sampling.
--
--   Differences from the source:
--   - reading: "for any decision function δ other than Bayes'" → for every δ that is not a Bayes decision function (fails (2.6) at some outcome with π0p0(b) ≠ π1p1(b)); reason: (2.6) allows anything on ties, so a δ differing from a fixed δB only at ties is itself Bayes' and has the same error; the proof's "the only nonzero terms … occur when δ(b) ≠ δB(b) and π0p0(b) ≠ π1p1(b)" is this reading; the non-strict inequality for every δ is the "optimal" of the same paragraph
--   - encoding: outcome set {1, …, n} → arbitrary finite type B; reason: every finite set is in bijection with some {1, …, n}, and IsDist forces it to be nonempty; no instance changes
--   - encoding: δ : {1, …, n} → {0, 1} with Pe(δ) given by (2.3) → δ : B → Fin 2 with errorProb given by (2.7), δ(b) cast to ℝ; reason: (2.7) is the source's own rewriting of (2.3); no instance changes
--   - encoding: Bayes' decision function δB of (2.6), with "anything" on ties → predicate IsBayesDecision, the statement quantified over every δB satisfying it; reason: (2.6) leaves ties free, so the predicate is exactly the family of rules (2.6) describes
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.1, eq. (2.9), p.14 (PDF p.23)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_errorProb
import Definitions.Def_FuchsThesis_Chernoff_IsBayesDecision

open CalibratedCE.Forecast

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.1, eq. (2.9), p.14 (PDF p.23): Bayes' decision function is
optimal, `Pe(δ) > Pe(δB)` for any decision function `δ` other than Bayes'.

Setting (p.13): one sample from `p0` or `p1` on a finite outcome set, priors `π0, π1 ≥ 0`,
`π0 + π1 = 1`. For every Bayes decision function `δB` (any tie-breaking) and every decision
function `δ`: `Pe(δB) ≤ Pe(δ)`, and the inequality is strict when `δ` is not a Bayes decision
function.

**Formalization Note.** "Other than Bayes'" is read as "not a Bayes decision function": since
(2.6) allows anything on ties, a `δ` that differs from a given `δB` only at ties is itself a Bayes
decision function and has the same error probability. -/
theorem eq_2_9 {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (δB : B → Fin 2) (hB : IsBayesDecision π0 π1 p0 p1 δB) (δ : B → Fin 2) :
    errorProb π0 π1 p0 p1 δB ≤ errorProb π0 π1 p0 p1 δ ∧
      (¬ IsBayesDecision π0 π1 p0 p1 δ →
        errorProb π0 π1 p0 p1 δB < errorProb π0 π1 p0 p1 δ) := by sorry

end FuchsThesis.Chernoff
