-- Prove2me | Theorems.Thm_MinSumFPT_theorem_25
-- name    : MinSumFPT.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:12.476199+00:00
-- url     : https://prove2.me/theorems/173d0bbd-bb57-462f-b283-653664f9362c
-- title:
--   Theorem 25 — sublinear $(1-\varepsilon)$-approximation of metric MAX $k$-CUT
-- statement:
--   There is a single randomized program, taking $n,k,\varepsilon,\delta$ as input, and a constant $C$ such that for all $n,k\ge1$, $\varepsilon,\delta\in(0,1)$ and every pseudometric $d$ on $n$ points:
--
--   1. on every random tape it halts within
--   $$
--   C\cdot\big(\varepsilon^{-2}\,n\log_2(2+n/\delta)+\varepsilon^{-3}\,n\,k^4\big)+k^{C\varepsilon^{-2}}
--   $$
--   steps, with a partition of the points into $k$ clusters (every label used when $k\le n$);
--   2. with probability at least $1-\delta$ the partition's cut value is at least $(1-\varepsilon)\cdot\mathrm{maxcut}_k(d)$.
--
--   Stage 3 uses this scheme to split the points of each connected component of the conflict graph. Because the cut objective is the complement of the minsum objective, an additive guarantee for the cut gives one for the clustering.
--
--   **Formalization Note** The program runs on `MinSumFPT.Machine`. The failure event has outer measure at most $\delta$ under the tape law. Cut values count ordered pairs.
--
--   Differences from the source:
--   - generalization: a finite metric space (A, d) → every pseudometric d; reason: Theorem 1's proof applies Theorem 25 to sub-instances of a semi-metric input; every metric is a pseudometric
--   - reading: time O(ε⁻²·n·log(n/δ)) + O(ε⁻³·n·k⁴) + k^{O(ε⁻²)} → C·(ε⁻²·n·log₂(2 + n/δ) + ε⁻³·n·k⁴) + k^{C·ε⁻²} on every tape; reason: one constant for all O's; log read as log₂(2 + x) ≥ 1; worst-case reading
--   - reading: a (1 − ε)-approximation with failure probability δ (ranges not stated) → ε, δ ∈ (0,1); cut ≥ (1 − ε)·maxcut except on tapes of outer measure ≤ δ; reason: the ranges in which the statement is meaningful
--   - reading: a partition A = C₁ ⊔ ⋯ ⊔ C_k → a labelling into k labels, surjective when k ≤ n; reason: a partition into k clusters; moving a point into an empty cluster never lowers the cut
--   - encoding: arithmetic operations, d(x,y) a single operation → steps of MinSumFPT.Machine, every instruction one unit, d read only through dist; reason: the page names no machine; no floor, log, exp or sqrt, so the bound is at least as strong
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 25, p.38

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_labCost

namespace MinSumFPT

/-- Theorem 25 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 25, p.38): there is a randomized algorithm that computes a
`(1 − ε)`-approximation to the optimal metric MAX k-CUT solution in time
`O(ε⁻² ⋅ n ⋅ log(n/δ)) + O(ε⁻³ ⋅ n ⋅ k⁴) + k^{O(ε⁻²)}`, where `δ` is the failure probability.

**Formalization Note.** One program of `MinSumFPT.Machine` (inputs `n, k, ε, δ`); on every tape it
halts within `C ⋅ (ε⁻² ⋅ n ⋅ log₂(2 + n/δ) + ε⁻³ ⋅ n ⋅ k⁴) + k^{C ⋅ ε⁻²}` steps with a labelling into
`k` labels (a partition into `k` clusters, every label used when `k ≤ n`), and the tapes on which
the cut value is below `(1 − ε) ⋅ maxCut d k` have outer measure at most `δ`. Cut values count
ordered pairs. `d` is a pseudometric (the page says metric). -/
theorem theorem_25 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (n k : ℕ) (ε δ : ℝ) (d : Fin n → Fin n → ℝ), 1 ≤ n → 1 ≤ k → 0 < ε → ε < 1 →
        0 < δ → δ < 1 → MinSumClust.IsPseudometric d →
        (∀ ω : ℕ → ℝ, ∃ (t : ℕ) (σ : Fin n → Fin k), OutputsLabelling (run P n k ε δ d ω t) σ ∧
          ((run P n k ε δ d ω t).work : ℝ) ≤
            C * (ε⁻¹ ^ 2 * n * Real.logb 2 (2 + n / δ) + ε⁻¹ ^ 3 * n * (k : ℝ) ^ 4) +
              (k : ℝ) ^ (C * ε⁻¹ ^ 2) ∧
          (k ≤ n → Function.Surjective σ)) ∧
        tapeLaw {ω | ∃ (t : ℕ) (σ : Fin n → Fin k), OutputsLabelling (run P n k ε δ d ω t) σ ∧
            cutVal d σ < (1 - ε) * maxCut d k} ≤ ENNReal.ofReal δ := by sorry

end MinSumFPT
