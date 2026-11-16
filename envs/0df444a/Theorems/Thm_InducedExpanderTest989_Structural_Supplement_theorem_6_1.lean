-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_theorem_6_1
-- name    : InducedExpanderTest989.Structural.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:04.016409+00:00
-- url     : https://prove2.me/theorems/282e7337-d44e-4b64-96c4-db59a3900c13
-- title:
--   Theorem 6.1 — query lower bound Ω(n^{1/2+c_{κ,ϕ}µ}) for structural testing
-- statement:
--   Let $d_0=512$. Fix $\alpha\in(0,1]$, $\kappa\in(0,1)$ and $\phi\in(0,9/20]$, and put
--   $$q=2^{\lceil\log_2(2/\kappa)\rceil},\qquad c_{\kappa,\phi}=\frac{q\kappa\phi^2}{16(q-1)\ln d_0}.$$
--   There are a constant $A=A(\alpha,\kappa,\phi)>0$ and an integer $n_0=n_0(\alpha,\kappa,\phi)$ such that the following holds for every $n\ge n_0$ and every $0<\mu\le1$. Suppose a randomized adaptive algorithm $\mathcal A$ with unrestricted computation, on simple graphs on $[n]$ of maximum degree at most $d_0$, accepts every graph in $\mathcal P_{\alpha,\phi}$ with probability at least $2/3$ and rejects every graph outside $\mathcal P_{\kappa\alpha,\mu\phi^2}$ with probability at least $2/3$ (conductance normalized by $d_0$). Then there are a graph $G$ satisfying one of the two promises and an adjacency-list ordering of $G$ on which, with positive probability over the internal randomness,
--   $$\#\{\text{adjacency-list queries of }\mathcal A\}>A\,n^{1/2+c_{\kappa,\phi}\mu}.$$
--   In particular the worst-case query complexity exceeds $A\,n^{1/2+c_{\kappa,\phi}\mu}$; the constants do not depend on $\mu$.
--
--   Together with Theorem 4.1 this nearly determines the best rejection threshold attainable with about $\sqrt n$ queries. This is a companion theorem of the mission; it is not used in the proof of the goal.
--
--   **Formalization Note** Algorithms are probability laws on arbitrary transcript-to-move strategies (the mission's `RandAlg`), so free uniform vertex samples and unrestricted computation are included. Rejection with probability at least $2/3$ is read as acceptance probability at most $1/3$. Query counts lie in $\{0,1,\dots\}\cup\{\infty\}$, a run that never halts counting $\infty$; $\lceil\cdot\rceil$ is the ceiling of the real base-2 logarithm and $\ln$ the natural logarithm.
--
--   Differences from the source:
--   - generalization: rejects every NO graph with probability at least 2/3 → accepts every NO graph with probability at most 1/3; reason: a weaker hypothesis on the algorithm (a non-halting run is neither), so the theorem covers every algorithm the source covers
--   - generalization: worst-case query complexity over promise graphs and internal randomness exceeds A n^{1/2+cµ} → some promise graph with some valid adjacency list has positive probability of more than A n^{1/2+cµ} queries; reason: positive probability gives a random tape exceeding the bound, which is the source's conclusion
--   - encoding: a randomized adaptive algorithm with unrestricted computation → a probability measure on arbitrary maps from transcripts to moves, queries counted in ℕ∞; reason: every algorithm with a random seed pushes forward to such a law
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.34 (PDF p.36), Theorem 6.1, eq. (22); informal Theorem 1.2 p.4 (PDF p.6)

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_QueryAlgorithms

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

open MeasureTheory

/-- Peng–Shen, STOC 2027 #989, Theorem 6.1 (p. 34, PDF 36). `d₀ = 512`,
`q = 2^⌈log₂(2/κ)⌉`, `c_{κ,ϕ} = qκϕ²/(16(q − 1) ln d₀)` (22). Every correct randomized adaptive
tester has, on some graph satisfying one of the promises (with some valid adjacency list), positive
probability of making more than `A n^{1/2 + c_{κ,ϕ} µ}` queries. `A` and `n₀` depend only on
`α, κ, ϕ`. -/
theorem theorem_6_1 :
    ∀ α κ ϕ : ℝ, 0 < α → α ≤ 1 → 0 < κ → κ < 1 → 0 < ϕ → ϕ ≤ 9/20 →
      ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
        ∀ 𝒜 : RandAlg n 512,
          IsCorrectTester 𝒜 (fun G => HasCore 512 G α ϕ)
            (fun G => ¬ HasCore 512 G (κ * α) (μ * ϕ ^ 2)) →
          ∃ (G : SimpleGraph (Fin n)) (O : Oracle n 512),
            DegreeBound 512 G ∧ IsAdjacencyList G O ∧
            (HasCore 512 G α ϕ ∨ ¬ HasCore 512 G (κ * α) (μ * ϕ ^ 2)) ∧
            0 < (𝒜 : Measure (QStrategy n 512))
              {s | ENNReal.ofReal (A * (n : ℝ) ^ ((1 : ℝ) / 2 +
                  ((2 : ℝ) ^ ⌈Real.logb 2 (2 / κ)⌉₊ * κ * ϕ ^ 2 /
                    (16 * ((2 : ℝ) ^ ⌈Real.logb 2 (2 / κ)⌉₊ - 1) * Real.log 512)) * μ)) <
                ((queryCount s O : ℕ∞) : ℝ≥0∞)} := by sorry

end InducedExpanderTest989.Structural.Supplement
