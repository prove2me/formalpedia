-- Prove2me | Theorems.Thm_NaiveLearn_OverMatch_theorem_1
-- name    : NaiveLearn.OverMatch.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:19.480974+00:00
-- url     : https://prove2.me/theorems/d99931eb-d32c-478d-a274-5f1eb9c77aac
-- title:
--   Theorem 1, p. 9 — a fully mixing continuous decision rule, differentiable at 0 or 1, yields agreement
-- statement:
--   Let $\sigma:[0,1]\to[0,1]$ be a decision rule such that
--
--   1. $\sigma(0)=0$ and $\sigma(1)=1$;
--   2. $\sigma(x)\in(0,1)$ for every $x\in(0,1)$;
--   3. $\sigma$ is continuous on $[0,1]$;
--   4. $\sigma$ is differentiable at $0$ or at $1$ (one-sided, within $[0,1]$).
--
--   Then $\sigma$ satisfies agreement: for every number of agents $m$, every weight matrix $W$ of a strongly connected network (row-stochastic, irreducible, $w_{ii}>0$), every $\epsilon\in(0,1]$ and every initial belief $\mathbf x^1\in[0,1]^m$, the random $\epsilon$-DeGroot process with decision rule $\sigma$ satisfies
--   $$
--   \Pr\big[\exists\,t^*,\ \exists\,a^*\in\{0,1\}:\ a_i^t=a^*\ \text{for all } i\in V \text{ and all } t\ge t^*\big]=1 .
--   $$
--
--   In particular the probability-matching rule $\sigma(x)=x$ yields agreement, which the analysis of the $\epsilon$-DeGroot process in Lemma 5 relies on.
--
--   **Formalization Note** Lean time $0$ is the paper's period $1$. "Strongly connected network $(G,W)$" is read with the model's standing assumptions on $W$ (p. 6), including $w_{ii}>0$.
-- source:
--   Arieli, Babichenko & Mueller-Frank, Naive Learning Through Probability Over-Matching, SSRN working paper 3338015 (version of August 3, 2020), p. 9, Theorem 1 and Definition 1

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace NaiveLearn.OverMatch

/-- Theorem 1, p. 9: a decision rule `σ` with (i) `σ 0 = 0`, `σ 1 = 1`, (ii) `σ x ∈ (0, 1)` for
`x ∈ (0, 1)`, (iii) `σ` continuous on `[0, 1]`, (iv) `σ` differentiable (within `[0, 1]`) at `0` or
at `1`, satisfies agreement: for every network, every `ε ∈ (0, 1]` and every initial belief
`x¹ ∈ [0, 1]^m`, almost surely all agents eventually play one common action. -/
theorem theorem_1 (σ : ℝ → ℝ) (h0 : σ 0 = 0) (h1 : σ 1 = 1)
    (hint : ∀ x ∈ Set.Ioo (0 : ℝ) 1, σ x ∈ Set.Ioo (0 : ℝ) 1)
    (hcont : ContinuousOn σ (Set.Icc 0 1))
    (hdiff : DifferentiableWithinAt ℝ σ (Set.Icc 0 1) 0 ∨
      DifferentiableWithinAt ℝ σ (Set.Icc 0 1) 1) :
    ∀ (m : ℕ) (W : Matrix (Fin m) (Fin m) ℝ), IsWeightMatrix W →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ x1 : Fin m → ℝ, (∀ i, x1 i ∈ Set.Icc (0 : ℝ) 1) →
        EventualAgreement σ ε W x1 := by sorry

end NaiveLearn.OverMatch
