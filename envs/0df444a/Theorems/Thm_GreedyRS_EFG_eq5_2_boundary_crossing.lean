-- Prove2me | Theorems.Thm_GreedyRS_EFG_eq5_2_boundary_crossing
-- name    : GreedyRS.EFG.eq5_2_boundary_crossing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:42.468115+00:00
-- url     : https://prove2.me/theorems/de13d4c9-ee1c-4139-996c-b8819b7e4cc4
-- title:
--   (5.2), p. 23 — PCS ≥ Pr{Σ_{i≥2} N_i(X̄₁*(n₀); n₀) + N₁*(n₀) ≤ B} for the EFG procedure
-- statement:
--   Consider the explore-first greedy procedure with $k$ alternatives, exploration size $n_0 \ge 1$ and total budget $B$, run on an arbitrary array of observations $X_{ij}$ on a probability space. Let $\bar X_i(n)$ be the running average of alternative $i$, let
--   $$\bar X_1^*(n_0) = \min_{n \ge n_0} \bar X_1(n), \qquad N_1^*(n_0) = \arg\min_{n\ge n_0} \bar X_1(n),$$
--   and $N_i(\bar X_1^*(n_0); n_0) = \inf\{n \ge n_0 : \bar X_i(n) < \bar X_1^*(n_0)\}$ for $i = 2, \dots, k$. Then
--   $$\mathrm{PCS} \ \ge\ \Pr\Big\{\sum_{i=2}^{k} N_i\big(\bar X_1^*(n_0); n_0\big) + N_1^*(n_0) \le B\Big\}.$$
--
--   This boundary-crossing inequality reduces the PCS of the EFG procedure to a statement about independent running-average processes, one per alternative.
--
--   **Formalization Note** Alternatives are $0, \dots, k-1$ with $0$ the paper's alternative 1. The inequality is stated for every measure and every observation array: under the smallest-index tie rule the event on the right is contained, path by path, in the event of correct selection. Argmins and crossing times are $\mathbb N\cup\{\infty\}$-valued; when the minimum is not attained, $N_1^*(n_0) = \infty$ and the event fails.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 23, Equation (5.2)

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem eq5_2_boundary_crossing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) (k n0 B : ℕ) (hn0 : 1 ≤ n0) :
    P {ω | (∑ i ∈ Finset.Ico 1 k,
          GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean (fun i j => X i j ω) i)
            (GreedyRS.Greedy.boundary (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0) n0) +
        GreedyRS.Greedy.argminFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 ≤ (B : ℕ∞)}
      ≤ GreedyRS.Greedy.pcs P X k n0 B := by sorry

end GreedyRS.EFG
