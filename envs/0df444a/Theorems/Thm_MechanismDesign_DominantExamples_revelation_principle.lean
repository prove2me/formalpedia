-- Prove2me | Theorems.Thm_MechanismDesign_DominantExamples_revelation_principle
-- name    : MechanismDesign.DominantExamples.revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T01:29:40.023143+00:00
-- url     : https://prove2.me/theorems/d33cc6dc-a362-4580-b402-77b0d2fb9de0
-- title:
--   Proposition 4.1 — revelation principle for dominant strategy mechanisms
-- statement:
--   Consider the single unit auction with type interval $[\underline\theta,\bar\theta]$. A **general mechanism** gives each buyer $i$ a set $S_i$ of messages and assigns to every message profile $s = (s_j)_{j \in I}$ an outcome: the probabilities $\alpha_i(s)$ with which each buyer $i$ obtains the good, forming a point of $\Delta$ ($\alpha_i(s) \ge 0$, $\alpha_i(s) \le 1$, $\sum_i \alpha_i(s) \le 1$), and the expected payments $p_i(s)$. A strategy for buyer $i$ maps each type $\theta_i$ to a message $\sigma_i(\theta_i) \in S_i$.
--
--   Suppose that for each type $\theta_i$ of each buyer $i$ the message $\sigma_i(\theta_i)$ is a **dominant strategy**: for every message profile $s$ of the others and every alternative message $s_i' \in S_i$,
--   $$\theta_i\,\alpha_i(\sigma_i(\theta_i), s_{-i}) - p_i(\sigma_i(\theta_i), s_{-i}) \ \ge\ \theta_i\,\alpha_i(s_i', s_{-i}) - p_i(s_i', s_{-i}).$$
--   Then there is a direct mechanism $(q, t_1,\dots,t_N)$ that is dominant strategy incentive-compatible — truth telling is a dominant strategy in it — and that reproduces the outcome of $\sigma$ at every type vector: for all $\theta \in \Theta$ and all $i$,
--   $$q_i(\theta) = \alpha_i(\sigma_1(\theta_1),\dots,\sigma_N(\theta_N)), \qquad t_i(\theta) = p_i(\sigma_1(\theta_1),\dots,\sigma_N(\theta_N)).$$
--
--   The result lets every subsequent statement of Chapter 4 restrict attention to direct mechanisms that are dominant strategy incentive-compatible.
--
--   **Formalization Note** The book does not formalize a general mechanism (p.79). It is modelled here in strategic form: arbitrary message types `S i`, pure messages, and an outcome function returning allocation probabilities and expected payments. A randomized behaviour plan in a game tree is covered by taking the plan itself as the message and its induced expected allocation and payments as the outcome. Dominance is required against every message profile of the other buyers, not only against the profiles their strategies produce. The direct mechanism is not assumed to be given: its existence is the conclusion.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.79–80, Proposition 4.1

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

namespace MechanismDesign.DominantExamples

/-- Proposition 4.1 (Revelation Principle for Dominant Strategy Mechanisms), pp.79–80.
A general mechanism is given by message sets `S i`, one per buyer, and an outcome function
assigning to every message profile `s` the probabilities `alloc i s` with which buyer `i` gets
the good (a point of `Δ`) and the expected payments `pay i s`. The strategy `σ i` maps every
type of buyer `i` to a message, and `σ i θ_i` is dominant: it is optimal for type `θ_i` against
every message profile of the other buyers. Then there is a direct mechanism in which truth
telling is dominant (dominant strategy incentive compatibility) and which yields, at every type
vector, the same allocation probabilities and the same expected payments as `σ` in the
original mechanism. -/
theorem revelation_principle {ι : Type*} [Fintype ι] [DecidableEq ι] (E : AuctionSetting)
    {S : ι → Type*} (alloc pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (σ : (i : ι) → ℝ → S i)
    (h_dominant : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : (j : ι) → S j, ∀ s' : S i,
      x * alloc i (Function.update s i s') - pay i (Function.update s i s') ≤
        x * alloc i (Function.update s i (σ i x)) - pay i (Function.update s i (σ i x))) :
    ∃ M : AuctionMechanism E ι, M.IsDSIC ∧
      ∀ θ ∈ E.typeSpace ι, ∀ i,
        M.q i θ = alloc i (fun j => σ j (θ j)) ∧ M.t i θ = pay i (fun j => σ j (θ j)) := by sorry

end MechanismDesign.DominantExamples
