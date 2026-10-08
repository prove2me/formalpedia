-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_repeated_posted_price_optimal
-- name    : MechanismDesign.Dynamic.repeated_posted_price_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T05:54:28.942237+00:00
-- url     : https://prove2.me/theorems/755e0565-9ee1-41b4-bfb7-0c7824802c58
-- title:
--   Proposition 11.12 -- repeating the static posted price is an optimal dynamic mechanism
-- statement:
--   Consider $T\ge1$ periods, a discount factor $\delta\in[0,1)$, a buyer with a fixed valuation $\theta\in[\underline\theta,\bar\theta]$ with distribution function $F$ and density $f>0$, and let $p^*\in[\underline\theta,\bar\theta]$ maximize $p(1-F(p))$. Let $(\bar q^s,\bar t^s)$ be the posted-price mechanism: $\bar q^s(\theta)=1$, $\bar t^s(\theta)=p^*$ if $\theta\ge p^*$, and $\bar q^s(\theta)=0$, $\bar t^s(\theta)=0$ if $\theta<p^*$.
--
--   Then the dynamic direct mechanism $(q^*,t^*)$ with $q^*_\tau(\theta)=\bar q^s(\theta)$ and $t^*_\tau(\theta)=\bar t^s(\theta)$ for all $\tau=1,\dots,T$ is an optimal selling mechanism: it is incentive-compatible and individually rational, and
--   $$\int_{\underline\theta}^{\bar\theta}\sum_{\tau=1}^{T}\delta^{\tau-1}t_\tau(\theta)f(\theta)\,d\theta\le\int_{\underline\theta}^{\bar\theta}\sum_{\tau=1}^{T}\delta^{\tau-1}t^*_\tau(\theta)f(\theta)\,d\theta$$
--   for every incentive-compatible and individually rational dynamic direct mechanism $(q,t)$.
--
--   With full commitment and static information, the optimal dynamic mechanism has no real dynamics: it does not respond to the buyer's purchases.
--
--   **Formalization Note** Optimality is among admissible (measurable) mechanisms with randomized allocations $q_\tau\in[0,1]$. The condition $T\ge1$ is the book's indexing $\tau=1,\dots,T$.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.230, Proposition 11.12

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_RepeatedSale

namespace MechanismDesign.Dynamic

/-- **Proposition 11.12**, p.230. Let `T ≥ 1` periods, discount factor `δ ∈ [0, 1)`, and
`p* ∈ [θ̲, θ̄]` maximize `p(1 − F(p))`. The (dynamic) direct mechanism `(q*, t*)` with
`q*_τ(θ) = q̄ˢ(θ)` and `t*_τ(θ) = t̄ˢ(θ)` for all `τ = 1, …, T` — the posted price `p*` in every
period — is an optimal selling mechanism: it is incentive-compatible and individually rational,
and its expected discounted revenue is at least that of every (admissible) incentive-compatible,
individually rational dynamic direct mechanism. -/
theorem repeated_posted_price_optimal {θlo θhi : ℝ} (D : ValuationDist θlo θhi) (T : ℕ)
    (hT : 0 < T) (δ : ℝ) (hδ : δ ∈ Set.Ico (0 : ℝ) 1) (pstar : ℝ)
    (hp : pstar ∈ Set.Icc θlo θhi)
    (hmax : IsMaxOn (fun p => p * (1 - D.F p)) (Set.Icc θlo θhi) pstar) :
    (repeatedPostedPrice T θlo θhi pstar).Admissible ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIC δ ∧
      (repeatedPostedPrice T θlo θhi pstar).IsIR δ ∧
      ∀ m : RepMechanism T θlo θhi, m.Admissible → m.IsIC δ → m.IsIR δ →
        m.revenue D δ ≤ (repeatedPostedPrice T θlo θhi pstar).revenue D δ := by sorry

end MechanismDesign.Dynamic
