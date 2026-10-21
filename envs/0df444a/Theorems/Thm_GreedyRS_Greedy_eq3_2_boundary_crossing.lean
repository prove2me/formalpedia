-- Prove2me | Theorems.Thm_GreedyRS_Greedy_eq3_2_boundary_crossing
-- name    : GreedyRS.Greedy.eq3_2_boundary_crossing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:08.882448+00:00
-- url     : https://prove2.me/theorems/bde635f4-e9cc-4c83-a9c2-ddfc48cafb96
-- title:
--   (3.2), p. 12 — PCS ≥ Pr{Σ_{i=2}^k N_i(X̄₁*) + N₁* ≤ B}: the boundary-crossing lower bound
-- statement:
--   Consider the greedy procedure on alternatives $1,\dots,k$ with total budget $B$, run on an arbitrary array of observations $X_{ij}$ (no distributional assumption is needed). Write $\bar X_i(n)$ for the running average of alternative $i$ after $n$ observations, and let
--   1. $\bar X_1^*=\min_{n\ge1}\bar X_1(n)$ be the minimum of the best alternative's running average (the *boundary*),
--   2. $N_1^*=\arg\min_{n\ge1}\bar X_1(n)$ the first time it is attained ($\infty$ if never),
--   3. $N_i(\bar X_1^*)=\inf\{n\ge1:\bar X_i(n)<\bar X_1^*\}$ the *boundary-crossing time* of alternative $i\ge2$ ($\infty$ if never).
--
--   Then the event $\{\sum_{i=2}^kN_i(\bar X_1^*)+N_1^*\le B\}$ implies a correct selection, and therefore
--   $$\mathrm{PCS}\ \ge\ \Pr\Bigl\{\sum_{i=2}^kN_i(\bar X_1^*)+N_1^*\le B\Bigr\}.\qquad(3.2)$$
--
--   This is the paper's boundary-crossing perspective: it replaces the intractable dynamics of the greedy procedure by a condition on separate, per-alternative crossing times, and it is the starting point of the proof of Theorem 1.
--
--   **Formalization Note** The paper's alternative $1$ is Lean's index $0$, and $i=2,\dots,k$ is `Finset.Ico 1 k`. Ties in the arg max of the procedure go to the smallest index; with this rule the inclusion of events holds for every outcome, not just almost surely. Crossing times and the argmin are valued in $\mathbb N\cup\{\infty\}$; when $N_1^*=\infty$ the event fails, and when $N_1^*<\infty$ the boundary is the attained minimum.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 12, §3.2, (3.2)

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GreedyRS.Greedy
theorem eq3_2_boundary_crossing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ) (k B : ℕ) :
    P {ω | (∑ i ∈ Finset.Ico 1 k,
          crossBelow (runMean (fun i j => X i j ω) i)
            (boundary (runMean (fun i j => X i j ω) 0) 1) 1)
        + argminFrom (runMean (fun i j => X i j ω) 0) 1 ≤ (B : ℕ∞)}
      ≤ pcs P X k 1 B := by sorry
end GreedyRS.Greedy
