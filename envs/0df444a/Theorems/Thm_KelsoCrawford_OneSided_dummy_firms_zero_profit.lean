-- Prove2me | Theorems.Thm_KelsoCrawford_OneSided_dummy_firms_zero_profit
-- name    : KelsoCrawford.OneSided.dummy_firms_zero_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:38.473632+00:00
-- url     : https://prove2.me/theorems/97fa1876-cde9-4712-b762-f4cdc4285bc8
-- title:
--   Section 4 — dummy firms earn zero profit in the fictitious market strict core
-- statement:
--   Let $v$ be a coalition production function on a finite worker set, with nonnegative marginal production (MP′) and $v(\varnothing)=0$ (NFL). Let every worker's salary utility $\mu^i$ be strictly increasing and continuous. In the fictitious market with $m+1$ identical firms and $m$ workers, every firm earns zero profit at any strict-core allocation $A$:
--
--   $$\pi^j(A)=v(C^j)-\sum_{i\in C^j}s_i=0\qquad\text{for every firm }j.$$
--
--   Here $C^j$ is the set assigned to firm $j$ and $s_i$ is the salary of worker $i$. This fact connects two-sided firm feasibility to the one-sided aggregate budget.
--
--   **Formalization Note** All salaries are real and all workers are assigned; empty firms have profit $v(\varnothing)=0$. MP′ and utility regularity are standing assumptions in the paper's fictitious-market argument.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1493, Section 4, proof of Theorem 3, sentence beginning “note that dummy firms’ profits”

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_KelsoCrawford_OneSided_Fictitious

namespace KelsoCrawford.OneSided

theorem dummy_firms_zero_profit {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (μ : W → ℝ → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hμ : ∀ i, StrictMono (μ i) ∧ Continuous (μ i))
    (A : Allocation W (Fin (Fintype.card W + 1)))
    (hcore : (fictitious v μ).IsStrictCore KelsoCrawford.ContinuousCore.anySalary A) :
    ∀ j, profit v (A.hired j) A.sal = 0 := by sorry

end KelsoCrawford.OneSided
