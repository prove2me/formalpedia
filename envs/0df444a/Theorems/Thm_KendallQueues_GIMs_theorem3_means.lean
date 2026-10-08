-- Prove2me | Theorems.Thm_KendallQueues_GIMs_theorem3_means
-- name    : KendallQueues.GIMs.theorem3_means
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:46:01.405166+00:00
-- url     : https://prove2.me/theorems/a4d7305d-6ae7-46e3-a841-985e61f06df4
-- title:
--   Theorem III, p. 349 — the equilibrium means of Q and w
-- statement:
--   Consider GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$, exponential service of mean $E(v)=b>0$, transition matrix $P$ of (8)–(14), and $\rho=b/(sa)<1$. Let $\lambda$ be a root of $F(\lambda)=\lambda$ in $(0,1)$, let $\mu_0,\dots,\mu_{s-2}$ be such that the trial vector (15) satisfies the invariance equations for $1\le j\le s-1$, and let
--   $$\alpha=\frac{\sum\mu+1+\lambda}{\sum\mu+1/(1-\lambda)},\qquad \beta=\frac{\sum\mu+1}{\sum\mu+1/(1-\lambda)}.$$
--   Then the limiting distribution $\pi$ of the chain exists, and in this equilibrium the mean queue size is
--   $$E(Q)=\frac{1-\alpha}{1-\lambda},$$
--   and the mean waiting time satisfies
--   $$\frac{E(w)}{E(v)}=\frac{1-\beta}{s(1-\lambda)}.$$
--
--   **Formalization Note** $E(Q)=\sum_{n\ge1}n\Pr(Q=n)$ is stated as a convergent series. $E(w)$ is the integral of the tail $\Pr(w>t)=1-\Pr(w\le t)$ over $t>0$, asserted integrable; $E(v)=b$ is the mean service time of §2.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 349, Theorem III, eqs. (21)–(22)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- Theorem III, p. 349: with `λ`, `μ`, `α`, `β` as in Theorem II, in equilibrium
`E(Q) = (1 - α)/(1 - λ)` (21) and `E(w)/E(v) = (1 - β)/(s(1 - λ))` (22), where `E(v) = b`;
`E(w)` is the integral of the tail `P(w > t)` over `t > 0`. -/
theorem theorem3_means (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (hρ : rho s a b < 1)
    (P : TransitionMatrix) (hP : P.p = gimsMatrix s A b)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) (hF : F s A b lam = lam)
    (μ : Fin (s - 1) → ℝ)
    (hμ : ∀ j : ℕ, 1 ≤ j → j ≤ s - 1 →
      HasSum (fun α => trialVector s μ lam α * P.p α j) (trialVector s μ lam j)) :
    ∃ π : ℕ → ℝ, HasSum π 1 ∧
      (∀ i j, Tendsto (fun n => P.stepProb n i j) atTop (𝓝 (π j))) ∧
      HasSum (fun n : ℕ => (n : ℝ) * queueLaw s π n)
        ((1 - ((∑ k, μ k) + 1 + lam) / ((∑ k, μ k) + 1 / (1 - lam))) / (1 - lam)) ∧
      IntegrableOn (fun t => 1 - waitCDF s b π t) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), (1 - waitCDF s b π t)) / b =
        (1 - ((∑ k, μ k) + 1) / ((∑ k, μ k) + 1 / (1 - lam))) / (s * (1 - lam)) := by sorry

end KendallQueues.GIMs
