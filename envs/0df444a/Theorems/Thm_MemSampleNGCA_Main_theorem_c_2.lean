-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_theorem_c_2
-- name    : MemSampleNGCA.Main.theorem_c_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:41:05.691138+00:00
-- url     : https://prove2.me/theorems/d1db44cc-f0bc-40b5-a7de-f02f225fafa9
-- title:
--   Theorem C.2 — 2 ≤ C(8N)^{1/m} ≤ d/[1024 log(8MN)] and success 0.9 force B ≥ c·d²/(C²N^{2/m})
-- statement:
--   There is a universal constant $c>0$ with the following property. Let $m\ge2$ be an integer, and let $A$ be a probability measure on $\mathbb R$ satisfying Assumptions (A1)–(A2) with parameters $M$, $C>0$ and $m$. Let $N\ge1$ be an integer sample budget with
--   $$2\le C(8N)^{1/m}\le\frac{d}{1024\log(8MN)}.$$
--   Every single-pass streaming tester for the NGCA problem (Problem 1.2) with $B$ bits of memory and $N$ samples whose errors satisfy $P_{N(0,I_d)^{\otimes N}}(\widehat T=1)+\sup_{\theta\in S^{d-1}}P_{P_{A,\theta}^{\otimes N}}(\widehat T=0)\le1/5$ has
--   $$B\ge c\cdot\frac{d^2}{C^2N^{2/m}}.$$
--   In particular this holds for every tester with success probability at least $0.9$.
--
--   This is the appendix form of the main theorem (Theorem 1.4). The constant $c$ does not depend on $d,N,m,C,M,A$ or the algorithm.
--
--   Differences from the source:
--   - generalization: every single-pass streaming tester with success probability at least 0.9 → every tester with P_{N(0,I_d)}(T̂ = 1) + sup_θ P_{A,θ}(T̂ = 0) ≤ 1/5; reason: success at least 0.9 under each hypothesis gives an error sum at most 0.2, and so does an average success of at least 0.9 over the two hypotheses, so every reading of the source is a special case
--   - encoding: B = Ω(d²/(C²N^{2/m})) → ∃ c > 0, quantified before d, N, m, C, M, A, B, Ω and the algorithm, with c · d²/(C²N^{2/m}) ≤ B; reason: the proof states that the implicit constant is universal
--   - encoding: M ≥ 1 and C > 0 → not stated separately; reason: AssumptionA1 implies M ≥ 1, and AssumptionA2 contains C > 0
--   - encoding: single-pass streaming tester (Definition 1.7) → StreamingAlg B (ℝ^d) Ω for an arbitrary measurable space Ω : Type u; reason: as in Lemma B.2; the randomness space ranges over every universe
--   - encoding: Problem 1.2's probabilities and sup over θ ∈ S^{d−1} → outProb in ℝ≥0∞ and ⨆ over the image set ngcaAlternatives, with P_{A,θ} = γ_d with density g_A(⟨θ, ·⟩); reason: same values
--   - encoding: (8N)^{1/m}, N^{2/m}, log → Real.rpow and the natural Real.log; B : ℕ compared as a real; reason: Lean conventions; N ≥ 1 and M ≥ 1 make every logarithm and power well defined
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 25 (PDF 27), Theorem C.2; proof §C.1.2, pp. 27–29 (PDF 29–31)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_NGCA

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- Theorem C.2 (p. 25, PDF 27): there is a universal `c > 0` such that, for `A` satisfying
(A1)–(A2) with an integer `m ≥ 2`, every integer `N ≥ 1` with
`2 ≤ C (8N)^{1/m} ≤ d / [1024 log(8MN)]`, and every single-pass streaming tester for Problem 1.2
with total error `P₀(T̂ = 1) + sup_θ P_{A,θ}(T̂ = 0) ≤ 1/5` (success probability at least 0.9),
the memory satisfies `B ≥ c · d² / (C² N^{2/m})`. -/
theorem theorem_c_2.{u} : ∃ c : ℝ, 0 < c ∧
    ∀ (d N m : ℕ) (C M : ℝ) (A : Measure ℝ) [IsProbabilityMeasure A],
      1 ≤ N → 2 ≤ m → AssumptionA1 M A → AssumptionA2 C m A →
      2 ≤ C * ((8 * N : ℕ) : ℝ) ^ ((1 : ℝ) / m) →
      C * ((8 * N : ℕ) : ℝ) ^ ((1 : ℝ) / m) ≤ (d : ℝ) / (1024 * Real.log (8 * M * N)) →
      ∀ (B : ℕ) (Ω : Type u) [MeasurableSpace Ω] (alg : StreamingAlg B (Rd d) Ω),
        alg.testError N (gammaD d) (ngcaAlternatives d A) ≤ 1 / 5 →
        c * (d : ℝ) ^ 2 / (C ^ 2 * (N : ℝ) ^ ((2 : ℝ) / m)) ≤ (B : ℝ) := by sorry

end MemSampleNGCA.Main
