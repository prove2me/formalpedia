-- Prove2me | Theorems.Thm_MechanismDesign_Auctions_revelation_principle
-- name    : MechanismDesign.Auctions.revelation_principle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:44:16.241799+00:00
-- url     : https://prove2.me/theorems/4b7f607d-40f6-455c-b553-e1d1e1506fb2
-- title:
--   Proposition 3.1 -- revelation principle for single-unit auctions
-- statement:
--   Consider the single-unit auction environment with independent private values on $\Theta = [\underline\theta,\bar\theta]^N$. A general (indirect) mechanism $\Gamma$ gives each buyer $i$ a set $S_i$ of messages and assigns to every message profile $s = (s_1,\dots,s_N)$ an outcome: the probabilities $\mathrm{alloc}_i(s) \ge 0$ with $\sum_i \mathrm{alloc}_i(s) \le 1$ that buyer $i$ receives the good, and the expected transfers $\mathrm{pay}_i(s)$. A strategy profile $\sigma = (\sigma_i)$, $\sigma_i : [\underline\theta,\bar\theta] \to S_i$, is a Bayesian Nash equilibrium of $\Gamma$ if for every buyer $i$, every type $\theta_i$ and every message $s_i \in S_i$,
--   $$\theta_i\,\mathbb E_{\theta_{-i}}\big[\mathrm{alloc}_i(s_i,\sigma_{-i}(\theta_{-i}))\big] - \mathbb E_{\theta_{-i}}\big[\mathrm{pay}_i(s_i,\sigma_{-i}(\theta_{-i}))\big] \le \theta_i\,\mathbb E_{\theta_{-i}}\big[\mathrm{alloc}_i(\sigma_i(\theta_i),\sigma_{-i}(\theta_{-i}))\big] - \mathbb E_{\theta_{-i}}\big[\mathrm{pay}_i(\sigma_i(\theta_i),\sigma_{-i}(\theta_{-i}))\big].$$
--
--   **Proposition 3.1.** For every such mechanism and Bayesian Nash equilibrium $\sigma$ there is a direct mechanism $(q,t)$ for which truth-telling is a Bayesian Nash equilibrium — that is, $(q,t)$ is incentive-compatible — and which, at every type vector $\theta \in \Theta$, produces the same allocation probabilities and the same expected transfers:
--   $$q_i(\theta) = \mathrm{alloc}_i(\sigma(\theta)),\qquad t_i(\theta) = \mathrm{pay}_i(\sigma(\theta))\qquad\text{for all } i.$$
--
--   The revelation principle justifies restricting the search for optimal selling procedures to incentive-compatible direct mechanisms, which is what the rest of §3.2 does.
--
--   **Formalization Note** The message sets are arbitrary measurable spaces, the outcome functions and strategies are measurable, and the expected transfers are integrable for every unilateral deviation — the book leaves these implicit. Equilibria are in pure (type-contingent) strategies. The outcome of a message profile is recorded as the vector of allocation probabilities and expected transfers, which is all that risk-neutral buyers and the seller care about (the book notes deterministic transfers are without loss for the same reason). The direct mechanism is also shown to be well defined in the sense of the model file.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.34–35, Proposition 3.1

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.1 (Revelation Principle), p.34. A general mechanism is given by message sets
`S i`, an outcome function assigning to every message profile `s` the probabilities `alloc i s`
with which buyer `i` gets the good (a point of `Δ`) and the expected transfers `pay i s`; `σ` is a
Bayesian Nash equilibrium of the induced game of incomplete information. Then the direct
mechanism `θ ↦ (alloc (σ θ), pay (σ θ))` has truth-telling as a Bayesian Nash equilibrium
(it is incentive-compatible) and yields, at every type vector, the same allocation probabilities
and the same expected transfers as `σ` in the original mechanism. -/
theorem revelation_principle {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι)
    {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (alloc : ι → ((j : ι) → S j) → ℝ) (pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (h_alloc_meas : ∀ i, Measurable (alloc i)) (h_pay_meas : ∀ i, Measurable (pay i))
    (σ : (i : ι) → ℝ → S i) (hσ_meas : ∀ i, Measurable (σ i))
    (h_pay_int : ∀ i, Integrable (fun θ => pay i (fun j => σ j (θ j))) E.prior)
    (h_dev_int : ∀ i, ∀ s : S i,
      Integrable (fun θ => pay i (Function.update (fun j => σ j (θ j)) i s)) E.prior)
    (h_BNE : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : S i,
      x * ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i s) ∂E.prior
          - ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i s) ∂E.prior
        ≤ x * ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior
          - ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior) :
    ∃ m : DirectMechanism E, m.WellDefined ∧ m.IsIC ∧
      ∀ θ ∈ E.typeSpace, ∀ i,
        m.q i θ = alloc i (fun j => σ j (θ j)) ∧ m.t i θ = pay i (fun j => σ j (θ j)) := by sorry

end MechanismDesign.Auctions
