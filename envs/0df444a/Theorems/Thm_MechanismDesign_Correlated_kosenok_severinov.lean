-- Prove2me | Theorems.Thm_MechanismDesign_Correlated_kosenok_severinov
-- name    : MechanismDesign.Correlated.kosenok_severinov
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:45:34.338911+00:00
-- url     : https://prove2.me/theorems/bd76acde-e725-488c-b30f-e7895476bfbc
-- title:
--   Proposition 6.6 (Kosenok–Severinov) — Crémer–McLean plus identifiability: BIC and ex post budget balance with the same decision rule and interim payments
-- statement:
--   **Proposition 6.6 (Kosenok and Severinov 2008).** Let every type set $\Theta_i$ be finite and let the common prior $\mu$ give every type vector positive probability. Suppose that $\mu$ satisfies the Crémer–McLean condition and the identifiability condition. Consider any direct mechanism $(q, t_1,\dots,t_N)$ that is ex ante budget balanced,
--   $$\sum_{\theta\in\Theta}\mu(\theta)\sum_{i=1}^N t_i(\theta) = 0.$$
--   Then there is an equivalent direct mechanism $(q, t_1',\dots,t_N')$ that is Bayesian incentive-compatible and ex post budget balanced, $\sum_{i\in I} t'_i(\theta) = 0$ for every $\theta\in\Theta$. Equivalent means: the same decision rule $q$ and the same interim expected payments
--   $$\sum_{\theta_{-i}} t_i(\theta_i,\theta_{-i})\,\mu(\theta_{-i}\mid\theta_i) = \sum_{\theta_{-i}} t_i'(\theta_i,\theta_{-i})\,\mu(\theta_{-i}\mid\theta_i)\quad\text{for all } i,\ \theta_i.$$
--
--   This adds ex post budget balance to the conclusion of the Crémer–McLean theorem (Proposition 6.4), at the price of the identifiability condition.
--
--   **Formalization Note** The book says "equivalent" here has "the same meaning as, for example, in Proposition 6.3", whose definition compares expected payments report by report. Read literally that makes the proposition false (a report-by-report equivalent mechanism with the same decision rule has exactly the incentives of the original, so a mechanism that is not incentive compatible has no such equivalent). The notion used is the one Proposition 6.4 states (same decision rule, same interim payments at truthful reports), which coincides with the report-by-report one under independence and is what Kosenok and Severinov prove.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.127, Proposition 6.6 (Definitions 6.7 p.120, 6.8 p.126, 6.6 p.118)

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_FiniteModel

namespace MechanismDesign.Correlated

open FiniteTypes

/-- Börgers, Proposition 6.6 (p.127), after Kosenok and Severinov (2008). Types are finite and
every type vector has positive prior probability. If the prior `μ` satisfies the Crémer–McLean
and the identifiability conditions, then for every ex ante budget balanced direct mechanism
`(q, t)` there is a Bayesian incentive-compatible, ex post budget balanced direct mechanism
`(q, t')` with the same decision rule and the same interim expected payments. -/
theorem kosenok_severinov {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (hId : Identifiable μ) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A)
    (hBB : IsExAnteBB μ M) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' ∧ IsExPostBB M' := by sorry

end MechanismDesign.Correlated
