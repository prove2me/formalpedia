-- Prove2me | Theorems.Thm_MechanismDesign_Correlated_interim_cyclical_monotonicity
-- name    : MechanismDesign.Correlated.interim_cyclical_monotonicity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:44:21.885709+00:00
-- url     : https://prove2.me/theorems/905f44e6-f8d2-4093-a097-c0745dd135b1
-- title:
--   Proposition 6.1 — with independent types, q is Bayesian implementable iff interim cyclically monotone
-- statement:
--   **Proposition 6.1.** Let types be independent: the common prior on $\Theta = \prod_{i\in I}\Theta_i$ is a product $\rho_1\otimes\dots\otimes\rho_N$ of probability measures on the (measurable) type sets. Let $q : \Theta \to A$ be a decision rule with interim decision rules $Q_i(\theta_i)$, the distributions on $A$ of $q(\theta_i,\theta_{-i})$. Then there are payment rules $t_1,\dots,t_N$ such that $(q, t_1, \dots, t_N)$ is a Bayesian incentive-compatible direct mechanism if and only if $q$ is **interim cyclically monotone**: for every $i \in I$, every $k\in\mathbb N$ and every sequence $(\theta^1_i, \dots, \theta^k_i) \in \Theta_i^k$ with $\theta^k_i = \theta^1_i$,
--   $$\sum_{\kappa=1}^{k-1}\left(\int_A u_i(a,\theta_i^{\kappa+1})\,dQ_i(\theta_i^\kappa) - \int_A u_i(a,\theta_i^\kappa)\,dQ_i(\theta_i^\kappa)\right) \le 0.$$
--
--   This is Rochet's characterization of implementable decision rules (Proposition 5.2) at the interim level. Independence is what makes it apply: the lottery over alternatives and the expected payment that type $\theta_i'$ obtains by pretending to be $\theta_i$ are those of type $\theta_i$ itself.
--
--   **Formalization Note** The sequence is indexed $s_0, \dots, s_m$ with $s_m = s_0$ ($m = k-1$). The decision rule is required to be measurable with each $u_i(\cdot,\theta_i)$ integrable against each $Q_i(\theta_i')$, and the payment rules to have integrable sections $\theta_{-i}\mapsto t_i(\theta_i',\theta_{-i})$ — the measurability the book omits (note 2 to Ch. 2). Payments are not required to be jointly measurable.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.116, Proposition 6.1

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel

namespace MechanismDesign.Correlated

open MeasureTheory Indep

/-- Börgers, Proposition 6.1 (p.116). With independent types (the prior is the product of the type
distributions `ρ i`), a decision rule `q` is part of a Bayesian incentive-compatible direct mechanism
`(q, t₁, …, t_N)` if and only if `q` is interim cyclically monotone. -/
theorem interim_cyclical_monotonicity {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*} [MeasurableSpace A]
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (u : ∀ i, A → Θ i → ℝ)
    (q : (∀ i, Θ i) → A) (hq : IsDecisionRule ρ u q) :
    (∃ t : ι → (∀ i, Θ i) → ℝ, IsTransferRule ρ t ∧ IsBIC ρ u ⟨q, t⟩) ↔
      IsInterimCyclicallyMonotone ρ u q := by sorry

end MechanismDesign.Correlated
