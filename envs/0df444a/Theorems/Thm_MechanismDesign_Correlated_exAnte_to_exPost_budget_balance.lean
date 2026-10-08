-- Prove2me | Theorems.Thm_MechanismDesign_Correlated_exAnte_to_exPost_budget_balance
-- name    : MechanismDesign.Correlated.exAnte_to_exPost_budget_balance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:44:36.990003+00:00
-- url     : https://prove2.me/theorems/58986fc3-4d30-421b-914a-dfd967275366
-- title:
--   Proposition 6.3 — with independent types, ex ante budget balance can be replaced by ex post budget balance
-- statement:
--   **Proposition 6.3.** Let types be independent (the prior $\mu$ is a product $\rho_1\otimes\dots\otimes\rho_N$) and let there be at least two agents. Then for every direct mechanism $(q, t_1,\dots,t_N)$ that is ex ante budget balanced,
--   $$\int_\Theta \sum_{i=1}^N t_i(\theta)\,d\mu(\theta) = 0,$$
--   there is an equivalent direct mechanism $(q, t_1',\dots,t_N')$ that is ex post budget balanced, $\sum_{i\in I} t'_i(\theta) = 0$ for every $\theta \in \Theta$. "Equivalent" means: the same decision rule, and for every agent $i$ and all $\theta_i,\theta_i'\in\Theta_i$ the same expected payment of agent $i$ conditional on type $\theta_i$ and report $\theta_i'$; with independent types this is the interim payment $T_i(\theta_i')$.
--
--   Equivalent mechanisms give every type of every agent the same expected utility from every report, so they share incentive compatibility and individual rationality; the result lets a designer impose budget balance only in expectation.
--
--   **Formalization Note** The hypothesis of at least two agents is **added**: the book's §6.2 does not restate Chapter 3's $N\ge 2$, and with one agent the claim is false (ex post balance forces $t_1' = 0$, while $T_1$ may be any nonconstant function with mean zero). Payment rules are required to have integrable sections $\theta_{-i}\mapsto t_i(\theta_i',\theta_{-i})$ (in both mechanisms) and, for ex ante budget balance, to be integrable against $\mu$ — the measurability the book omits (note 2 to Ch. 2).
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.118, Proposition 6.3 (with Definition 6.6 and the definition of "equivalent" on the same page)

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_IndepModel

namespace MechanismDesign.Correlated

open MeasureTheory Indep

/-- Börgers, Proposition 6.3 (p.118). With independent types (and at least two agents), for every
direct mechanism that is ex ante budget balanced there is an equivalent direct mechanism that is ex
post budget balanced. -/
theorem exAnte_to_exPost_budget_balance {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, MeasurableSpace (Θ i)] {A : Type*}
    (ρ : ∀ i, Measure (Θ i)) [∀ i, IsProbabilityMeasure (ρ i)] (hN : 2 ≤ Fintype.card ι)
    (M : DirectMechanism ι Θ A) (hM : IsTransferRule ρ M.t) (hBB : IsExAnteBB ρ M) :
    ∃ M' : DirectMechanism ι Θ A, IsTransferRule ρ M'.t ∧ Equivalent ρ M M' ∧ IsExPostBB M' := by sorry

end MechanismDesign.Correlated
