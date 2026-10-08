-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_lemma61
-- name    : NegativeDP.EssFinite.lemma61
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:36.049181+00:00
-- url     : https://prove2.me/theorems/71652726-41bb-40f5-ae99-e83a6407e64a
-- title:
--   Lemma 6.1 (N) — lim U^n0 ≥ sup over π̂-generated policies ≥ sup over π̂-generated stationary policies
-- statement:
--   Consider Strauch's negative dynamic programming problem: non-empty Borel state and action spaces $S$, $A$, a law of motion $q$, and a Borel return $r\le 0$ with $\int r(s,a,t)\,dq(t\mid s,a)>-\infty$. Let $\hat\pi=(f_1,f_2,\dots)$ be any Markov policy, i.e. any countable sequence of measurable maps $S\to A$, and let $U$ be its operator, $Uu=\sup_n T_n u$. A measurable $f:S\to A$ is **$\hat\pi$-generated** if there is a partition of $S$ into Borel sets $S_1,S_2,\dots$ with $f=f_n$ on $S_n$; a Markov policy is $\hat\pi$-generated if each of its maps is. Let $G(\hat\pi)$ be the set of $\hat\pi$-generated policies.
--
--   Then the pointwise limit $\lim_{n\to\infty}U^n0$ exists (with $U^0 0=0$), and at every state
--   $$\lim_{n\to\infty}U^n0\;\ge\;\sup_{\pi\in G(\hat\pi)}I(\pi)\;\ge\;\sup_{f^{(\infty)}\in G(\hat\pi)}I(f^{(\infty)}).$$
--
--   The paper states this for the discounted, positive and negative cases; this item is the negative case. No finiteness assumption on the actions is made. The three quantities are the limit of the optimal finite-horizon returns among $\hat\pi$-generated policies, the optimal infinite-horizon return among them, and the optimal return among $\hat\pi$-generated stationary policies; Example 6.1 of the paper shows that in the negative case all three may differ.
--
--   **Formalization Note** The existence of the limit is part of the statement (the paper takes it from Theorem 5.2 (e)), so the statement provides a function $w$ with $U^n0\to w$ pointwise in `EReal`. $G(\hat\pi)$ consists of non-random Markov plans whose every rule is $\hat\pi$-generated (`IsGeneratedPlan` of the published `Operators` module, with a measurable, pairwise disjoint, covering partition indexed from $0$, the piece `n` carrying `π̂ n`); the stationary $f^{(\infty)}\in G(\hat\pi)$ are those with $f$ $\hat\pi$-generated (`IsGenerated`). Suprema are in `EReal`.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 880, Lemma 6.1

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model

open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Lemma 6.1 (N), Strauch (1966), p. 880. For any Markov policy `π̂` with operator `U`,
`lim NegativeDP.OptEq.U^n 0` exists and `lim NegativeDP.OptEq.U^n 0 ≧ sup_{π ∈ G(π̂)} NegativeDP.Stationary.I(π) ≧ sup_{f^(∞) ∈ G(π̂)} NegativeDP.Stationary.I(f^(∞))`,
where `G(π̂)` is the set of `π̂`-generated (Markov) policies. -/
theorem lemma61 (P : NegativeDP.Stationary.Problem S A) (πhat : MarkovPlan S A) :
    ∃ w : S → EReal,
      (∀ s, Tendsto (fun n => (NegativeDP.OptEq.U P πhat)^[n] 0 s) atTop (𝓝 (w s))) ∧
      (∀ s, (⨆ σ : {σ : MarkovPlan S A // IsGeneratedPlan πhat σ}, NegativeDP.Stationary.I P σ.1.toPlan s) ≤ w s) ∧
      ∀ s, (⨆ f : {f : {g : S → A // Measurable g} // IsGenerated πhat f},
              NegativeDP.Stationary.I P (stationary f.1).toPlan s) ≤
            ⨆ σ : {σ : MarkovPlan S A // IsGeneratedPlan πhat σ}, NegativeDP.Stationary.I P σ.1.toPlan s := by sorry

end NegativeDP.EssFinite
