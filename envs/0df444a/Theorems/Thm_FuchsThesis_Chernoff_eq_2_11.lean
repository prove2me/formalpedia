-- Prove2me | Theorems.Thm_FuchsThesis_Chernoff_eq_2_11
-- name    : FuchsThesis.Chernoff.eq_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:17.462106+00:00
-- url     : https://prove2.me/theorems/2d4334ae-1dc2-4b27-b948-0d71c7042369
-- title:
--   Eqs. (2.10)–(2.11) — the Bayes error is $\sum_b \min\{\pi_0 p_0(b), \pi_1 p_1(b)\}$
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite outcome set $\{1,\dots,n\}$ and $\pi_0, \pi_1 \ge 0$ priors with $\pi_0 + \pi_1 = 1$. Write $p(b) = \pi_0 p_0(b) + \pi_1 p_1(b)$ for the total probability of outcome $b$ and $p(i \mid b) = \pi_i p_i(b) / p(b)$ for the posterior probabilities. For every Bayes decision function $\delta_B$, its probability of error $P_e = P_e(\delta_B)$ satisfies
--
--   $$
--   P_e = \sum_{b=1}^{n} p(b)\bigl(1 - \max\{p(0\mid b), p(1\mid b)\}\bigr) = \sum_{b=1}^{n} p(b) \min\{p(0\mid b), p(1\mid b)\} = \sum_{b=1}^{n} \min\{\pi_0 p_0(b), \pi_1 p_1(b)\}.
--   $$
--
--   The last expression is the concrete formula for the first distinguishability measure of the thesis, and it is the formula used for $P_e(N)$ in the Chernoff bound.
--
--   **Formalization Note** Lean's division returns $0$ when $p(b) = 0$; each posterior is multiplied by $p(b)$, so those terms are $0$ on both sides, as in the source.
--
--   Differences from the source:
--   - encoding: posterior p(i|b) = πi pi(b)/p(b), undefined where p(b) = 0 → Lean division with x/0 = 0; reason: every posterior is multiplied by p(b), so terms with p(b) = 0 vanish on both sides and no instance changes
--   - encoding: outcome set {1, …, n} → arbitrary finite type B; reason: every finite set is in bijection with some {1, …, n}, and IsDist forces it to be nonempty; no instance changes
--   - encoding: δ : {1, …, n} → {0, 1} with Pe(δ) given by (2.3) → δ : B → Fin 2 with errorProb given by (2.7), δ(b) cast to ℝ; reason: (2.7) is the source's own rewriting of (2.3); no instance changes
--   - encoding: Bayes' decision function δB of (2.6), with "anything" on ties → predicate IsBayesDecision, the statement quantified over every δB satisfying it; reason: (2.6) leaves ties free, so the predicate is exactly the family of rules (2.6) describes
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.1, eqs. (2.10)–(2.11), pp.14–15 (PDF pp.23–24)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_errorProb
import Definitions.Def_FuchsThesis_Chernoff_IsBayesDecision
import Definitions.Def_FuchsThesis_Chernoff_bayesError

open CalibratedCE.Forecast

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.1, eqs. (2.10)–(2.11), pp.14–15 (PDF pp.23–24).

With `p(b) = π0 p0(b) + π1 p1(b)` (2.5) and the posteriors `p(i|b) = πi pi(b) / p(b)` (2.4),
the probability of error `Pe` of Bayes' decision method satisfies
`Pe = ∑_b p(b) (1 − max{p(0|b), p(1|b)}) = ∑_b p(b) min{p(0|b), p(1|b)} = ∑_b min{π0 p0(b), π1 p1(b)}`.
`Pe` is the error probability (2.7) of any Bayes decision function `δB` (2.6).

**Formalization Note.** Lean's division gives `x / 0 = 0`; the posterior is then a junk value
exactly where `p(b) = 0`, and every such term is multiplied by `p(b) = 0`, so the chain is the
source's. -/
theorem eq_2_11 {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (δB : B → Fin 2) (hB : IsBayesDecision π0 π1 p0 p1 δB) :
    errorProb π0 π1 p0 p1 δB =
        ∑ b, (π0 * p0 b + π1 * p1 b) *
          (1 - max (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
                   (π1 * p1 b / (π0 * p0 b + π1 * p1 b))) ∧
      ∑ b, (π0 * p0 b + π1 * p1 b) *
          (1 - max (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
                   (π1 * p1 b / (π0 * p0 b + π1 * p1 b))) =
        ∑ b, (π0 * p0 b + π1 * p1 b) *
          min (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
              (π1 * p1 b / (π0 * p0 b + π1 * p1 b)) ∧
      ∑ b, (π0 * p0 b + π1 * p1 b) *
          min (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
              (π1 * p1 b / (π0 * p0 b + π1 * p1 b)) =
        bayesError π0 π1 p0 p1 := by sorry

end FuchsThesis.Chernoff
