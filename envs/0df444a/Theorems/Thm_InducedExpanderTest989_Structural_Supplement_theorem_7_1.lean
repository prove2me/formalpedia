-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_theorem_7_1
-- name    : InducedExpanderTest989.Structural.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:34.796848+00:00
-- url     : https://prove2.me/theorems/6ddffcf0-32b5-4882-a1e2-b04b3c91d75d
-- title:
--   Theorem 7.1 — linear query lower bound for exact-size structural testing
-- statement:
--   Fix $\alpha\in(0,1]$ and $\phi\in(0,1/2)$, and let $d\ge4$ be an even integer with
--   $$\frac{d-2\sqrt{d-1}-1}{2d}>\phi.\tag{44}$$
--   1. Such a $d$ exists for every $\phi\in(0,1/2)$, and $d=512$ satisfies (44) whenever $\phi\le9/20$.
--   2. There is an integer $n_1=n_1(\alpha,\phi,d)$ such that the following holds for every $n\ge n_1$ and every $0<\mu_n\le1$, with $k=\lceil\alpha n\rceil$. Suppose a randomized adaptive algorithm $\mathcal A$ with unrestricted computation accepts every simple graph in $\mathcal P_{\alpha,\phi}$ on $[n]$ of maximum degree at most $d$ with probability at least $2/3$, and rejects every such graph outside $\mathcal P_{\alpha,\mu_n\phi^2}$ with probability at least $2/3$. Then there is a graph $G_Y\in\mathcal P_{\alpha,\phi}$ on $[n]$ of maximum degree at most $d$, with an adjacency-list ordering, on which the expected number of adjacency-list queries of $\mathcal A$ is at least
--   $$\frac{k}{3(d+1)},$$
--   and on which $\mathcal A$ makes at least this many queries with positive probability; in particular its worst-case query complexity is at least this quantity. The bound holds even when uniform vertex samples are free.
--   3. If $\mu\phi^2\le\phi$, then $dn$ adjacency-list queries suffice: a deterministic procedure that reads the whole adjacency table and decides membership in $\mathcal P_{\alpha,\phi}$ by exhaustive search accepts every graph in $\mathcal P_{\alpha,\phi}$ and rejects every graph outside $\mathcal P_{\alpha,\mu\phi^2}$.
--
--   Without the size relaxation $\kappa<1$, testing for a large induced expander therefore needs a linear number of queries, whatever the rejection multiplier. This is a companion theorem of the mission; it is not used in the proof of the goal.
--
--   **Formalization Note** Algorithms are the mission's `RandAlg` (probability laws on arbitrary transcript-to-move strategies), so free uniform vertex samples and unrestricted computation are built in; rejection with probability at least $2/3$ is acceptance probability at most $1/3$, and the expected query count lies in $[0,\infty]$. The upper-bound clause is a deterministic strategy (`QStrategy`) that halts with the correct answer after at most $dn$ queries on every valid adjacency list.
--
--   Differences from the source:
--   - generalization: rejects every NO graph with probability at least 2/3 → accepts every NO graph with probability at most 1/3; reason: a weaker hypothesis on the algorithm, so the theorem covers every algorithm the source covers
--   - generalization: in particular, the worst-case query complexity is at least k/(3(d+1)) → on the same G_Y and adjacency list, at least k/(3(d+1)) queries with positive probability; reason: positive probability gives a random tape attaining the bound, which is the source's conclusion
--   - generalization: dn queries suffice (for the theorem's n ≥ n₁ and 0 < µ_n ≤ 1 with µ_nϕ² ≤ ϕ) → for every n and every real µ with µϕ² ≤ ϕ, a deterministic strategy that is always correct with at most dn queries; reason: exhaustive search works for every n and every such µ, and the source's case is an instance
--   - encoding: such a d exists; for ϕ ≤ 9/20 one may take d = 512 → for every ϕ ∈ (0, 1/2) there is an even d ≥ 4 with (44), and (44) holds at d = 512 for every ϕ ∈ (0, 9/20]; reason: 512 is even and at least 4
--   - encoding: an adaptive randomized algorithm with unrestricted computation, with free uniform vertex samples → a probability measure on arbitrary maps from transcripts to moves, queries counted in ℕ∞; reason: every algorithm with a random seed, including free vertex samples, pushes forward to such a law
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, pp.47–48 (PDF pp.49–50), Theorem 7.1, eq. (44)

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_QueryAlgorithms

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

open MeasureTheory

/-- Peng–Shen, STOC 2027 #989, Theorem 7.1 (pp. 47–48, PDF 49–50). Condition (44) is
`ϕ < (d − 2√(d − 1) − 1)/(2d)`. Clauses: (a) such an even `d ≥ 4` exists for every
`ϕ ∈ (0, 1/2)`; (b) `d = 512` satisfies (44) when `ϕ ≤ 9/20`; (c) the lower bound
`k/(3(d + 1))`, `k = ⌈αn⌉`, on the expected and on the worst-case number of queries on one
YES graph `G_Y`; (d) `dn` queries suffice when `µϕ² ≤ ϕ`. -/
theorem theorem_7_1 :
    (∀ ϕ : ℝ, 0 < ϕ → ϕ < 1/2 →
      ∃ d : ℕ, 4 ≤ d ∧ Even d ∧ ϕ < ((d : ℝ) - 2 * Real.sqrt ((d : ℝ) - 1) - 1) / (2 * d)) ∧
    (∀ ϕ : ℝ, 0 < ϕ → ϕ ≤ 9/20 →
      ϕ < ((512 : ℝ) - 2 * Real.sqrt ((512 : ℝ) - 1) - 1) / (2 * 512)) ∧
    (∀ α ϕ : ℝ, 0 < α → α ≤ 1 → 0 < ϕ → ϕ < 1/2 →
      ∀ d : ℕ, 4 ≤ d → Even d → ϕ < ((d : ℝ) - 2 * Real.sqrt ((d : ℝ) - 1) - 1) / (2 * d) →
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
        ∀ 𝒜 : RandAlg n d,
          IsCorrectTester 𝒜 (fun G => HasCore d G α ϕ) (fun G => ¬ HasCore d G α (μ * ϕ ^ 2)) →
          ∃ (G : SimpleGraph (Fin n)) (O : Oracle n d),
            DegreeBound d G ∧ IsAdjacencyList G O ∧ HasCore d G α ϕ ∧
            ENNReal.ofReal ((⌈α * n⌉₊ : ℝ) / (3 * (d + 1))) ≤ expectedQueries 𝒜 O ∧
            0 < (𝒜 : Measure (QStrategy n d))
              {s | ENNReal.ofReal ((⌈α * n⌉₊ : ℝ) / (3 * (d + 1))) ≤
                ((queryCount s O : ℕ∞) : ℝ≥0∞)}) ∧
    (∀ α ϕ : ℝ, 0 < α → α ≤ 1 → 0 < ϕ → ϕ < 1/2 →
      ∀ d : ℕ, 4 ≤ d → Even d → ϕ < ((d : ℝ) - 2 * Real.sqrt ((d : ℝ) - 1) - 1) / (2 * d) →
      ∀ (n : ℕ) (μ : ℝ), μ * ϕ ^ 2 ≤ ϕ →
        ∃ s₀ : QStrategy n d, ∀ G : SimpleGraph (Fin n), DegreeBound d G →
          ∀ O : Oracle n d, IsAdjacencyList G O →
            queryCount s₀ O ≤ (d * n : ℕ) ∧
            (HasCore d G α ϕ → Accepts s₀ O) ∧
            (¬ HasCore d G α (μ * ϕ ^ 2) → Rejects s₀ O)) := by sorry

end InducedExpanderTest989.Structural.Supplement
