-- Prove2me | Theorems.Thm_KendallQueues_GIMs_invariance_tail_iff
-- name    : KendallQueues.GIMs.invariance_tail_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:11.19753+00:00
-- url     : https://prove2.me/theorems/63557dc7-814c-44cd-bd80-c02817f6b15d
-- title:
--   §7, p. 348 — for j ≥ s the invariance equations of the trial vector reduce to F(λ) = λ
-- statement:
--   Consider GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$ and exponential service of mean $b>0$, with transition matrix $P=[p_{ij}]$ of (8)–(14). Let $0<\lambda<1$, let $\mu_0,\dots,\mu_{s-2}$ be arbitrary real numbers, and let
--   $$x=[\mu_0,\mu_1,\dots,\mu_{s-2},1,\lambda,\lambda^2,\lambda^3,\dots]$$
--   be the trial vector (15). Then for every $j\ge s$ the invariance equation
--   $$x_j=\sum_{\alpha=0}^{\infty}x_\alpha p_{\alpha j}$$
--   holds (the series converging to $x_j$) if and only if
--   $$F(\lambda)=\lambda,\qquad F(\lambda)=\int_0^\infty e^{-(1-\lambda)su/b}\,dA(u).$$
--
--   This reduces the infinitely many invariance equations for $j\ge s$ to the single equation (16) for $\lambda$.
--
--   **Formalization Note** The statement is about the matrix function `gimsMatrix s A b` directly. The $\mu$'s are indexed by `Fin (s - 1)`; for $s=1$ there are none.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 348, eqs. (15)–(17)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- §7, p. 348: for the trial vector (15) with `0 < x < 1` and any `μ`, each invariance equation
`x_j = ∑_α x_α p_{αj}` with `j ≥ s` is equivalent to `F(x) = x` (16)–(17). -/
theorem invariance_tail_iff (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (μ : Fin (s - 1) → ℝ) (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) (hj : s ≤ j) :
    HasSum (fun α => trialVector s μ x α * gimsMatrix s A b α j) (trialVector s μ x j) ↔
      F s A b x = x := by sorry

end KendallQueues.GIMs
