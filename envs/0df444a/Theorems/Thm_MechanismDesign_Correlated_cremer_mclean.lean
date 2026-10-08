-- Prove2me | Theorems.Thm_MechanismDesign_Correlated_cremer_mclean
-- name    : MechanismDesign.Correlated.cremer_mclean
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:45:11.869078+00:00
-- url     : https://prove2.me/theorems/7ae2a57c-c575-45e8-baa4-29b5f5b12e21
-- title:
--   Proposition 6.4 (Crémer–McLean) — under the Crémer–McLean condition every direct mechanism has a BIC version with the same decision rule and interim payments
-- statement:
--   **Proposition 6.4 (Crémer and McLean 1988).** Let every type set $\Theta_i$ be finite and let the common prior $\mu$ give every type vector positive probability, $\mu(\theta) > 0$. Suppose that $\mu$ satisfies the Crémer–McLean condition: for no agent $i$ and type $\theta_i$ is the conditional belief $\mu(\cdot\mid\theta_i)$ a nonnegative combination $\sum_{\theta_i'\ne\theta_i}\lambda(\theta_i')\,\mu(\cdot\mid\theta_i')$ of the beliefs of agent $i$'s other types. Consider **any** direct mechanism $(q,t)$, with arbitrary utilities $u_i(a,\theta_i)$ and an arbitrary set of alternatives $A$. Then there is a direct mechanism $(q, t')$ that is Bayesian incentive-compatible and equivalent to $(q,t)$, that is:
--
--   1. the two mechanisms have the same decision rule $q$;
--   2. the two mechanisms have the same interim expected payments:
--   $$\sum_{\theta_{-i}\in\Theta_{-i}} t_i(\theta_i,\theta_{-i})\,\mu(\theta_{-i}\mid\theta_i) = \sum_{\theta_{-i}\in\Theta_{-i}} t_i'(\theta_i,\theta_{-i})\,\mu(\theta_{-i}\mid\theta_i) \quad\text{for all } i\in I,\ \theta_i\in\Theta_i.$$
--
--   Every direct mechanism can thus be made Bayesian incentive-compatible without altering its decision rule or interim expected payments; in a single-unit auction with correlated values the seller can extract the full surplus.
--
--   **Formalization Note** The original mechanism is arbitrary (not assumed incentive compatible or individually rational). "Equivalent" is exactly items 1–2 as printed in the proposition: equality of interim payments at truthful reports. The report-by-report equivalence of Proposition 3.6 would keep every incentive of $(q,t)$ unchanged and make the result false for every mechanism that is not already incentive compatible.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.121, Proposition 6.4 (standing assumptions of §6.4.1 p.119; Definition 6.7 p.120)

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_FiniteModel

namespace MechanismDesign.Correlated

open FiniteTypes

/-- Börgers, Proposition 6.4 (p.121), after Crémer and McLean (1988). Types are finite and every
type vector has positive prior probability. If the prior `μ` satisfies the Crémer–McLean
condition, then for every direct mechanism `(q, t)` there is a Bayesian incentive-compatible direct
mechanism `(q, t')` with the same decision rule and the same interim expected payments
`∑_{θ₋ᵢ} tᵢ(θᵢ, θ₋ᵢ) μ(θ₋ᵢ | θᵢ) = ∑_{θ₋ᵢ} t'ᵢ(θᵢ, θ₋ᵢ) μ(θ₋ᵢ | θᵢ)` for all `i` and `θᵢ`. -/
theorem cremer_mclean {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' := by sorry

end MechanismDesign.Correlated
