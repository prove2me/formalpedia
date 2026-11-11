-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_theorem_1_4
-- name    : MemSampleNGCA.Main.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:40:55.891943+00:00
-- url     : https://prove2.me/theorems/8a9dd1c9-45ce-46bf-a79f-a6bb043de395
-- title:
--   Theorem 1.4 — every single-pass streaming NGCA tester with N samples needs B ≥ c·d²/(C²N^{2/m}) bits of memory
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $A$ be a probability measure on $\mathbb R$ satisfying Assumption A1 with parameter $M>0$ ($A\ll\gamma$ and $dA/d\gamma\in[0,M]$) and Assumption A2 with parameters $C\ge2$ and an integer $m\ge2$ ($\|U_\rho g_A\|_{L^\infty(\gamma)}\le1+C^m\rho^{2m}$ for all $\rho\in[0,1/\sqrt2]$, where $g_A=dA/d\gamma$ and $U_\rho$ is the Ornstein–Uhlenbeck operator). Let $N\ge1$ and
--   $$d\ge1024\,C\,(8N)^{1/m}\log(8MN).$$
--   Let a single-pass streaming algorithm with $B$ bits of memory solve the NGCA testing problem (Problem 1.2) with $N$ samples, i.e.
--   $$P_{N(0,I_d)^{\otimes N}}(\widehat T=1)+\sup_{\theta\in S^{d-1}}P_{P_{A,\theta}^{\otimes N}}(\widehat T=0)\le0.1.$$
--   Then
--   $$B\ge c\cdot\frac{d^2}{C^2N^{2/m}}.$$
--
--   This is the paper's main result: a quadratic-in-dimension memory lower bound for testing a hidden non-Gaussian direction with a near-linear number of samples. With $N=O(d)$ samples and constant $m,C$, it gives $B=\Omega(d^{2(1-1/m)})$, while storing the hidden direction takes only $\widetilde O(d)$ bits.
--
--   Differences from the source:
--   - encoding: there exists a universal constant c > 0 → ∃ c > 0 quantified before d, N, m, C, M, A, B, Ω and the algorithm; reason: "universal" means independent of all of them
--   - encoding: single-pass streaming algorithm (Definition 1.7) → StreamingAlg B (ℝ^d) Ω for an arbitrary measurable space Ω : Type u (states Fin B → Bool, measurable Upd depending on the index i, measurable Out, seeds i.i.d. from a probability measure R); reason: measurability is needed for the probabilities to exist; the randomness space ranges over every universe
--   - encoding: P_{A,θ} (Definition 1.1) → γ_d with density g_A(⟨θ, ·⟩), g_A = dA/dγ via rnDeriv; reason: the same measure
--   - encoding: solves Problem 1.2 (§1.3 criterion) → StreamingAlg.Solves: outProb in ℝ≥0∞, sup over θ ∈ S^{d−1} as ⨆ over the image set ngcaAlternatives, 0.1 as 1/10; reason: same values
--   - encoding: A1, A2 → AssumptionA1 (0 < M, A ≪ γ, dA/dγ ≤ M γ-a.e.) and AssumptionA2 (0 < C, ‖U_ρ g_A‖_{L∞(γ)} as eLpNorm ∞ for ρ ∈ [0, 1/√2]); reason: Radon–Nikodym derivatives are defined up to γ-null sets; under A1 the integrand of U_ρ g_A is bounded, so the Bochner integral is the paper's
--   - encoding: N samples → N ≥ 1; reason: log(8MN) is undefined at N = 0
--   - encoding: (8N)^{1/m}, N^{2/m}, log → Real.rpow and the natural Real.log; B : ℕ compared as a real; reason: Lean conventions
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 4 (PDF 6), Theorem 1.4 (proved as Theorem C.2, p. 25, PDF 27)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_NGCA

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- Theorem 1.4 (p. 4, PDF 6): there is a universal constant `c > 0` such that, whenever `A`
satisfies Assumption A1 with parameter `M` and Assumption A2 with an integer `m ≥ 2` and `C ≥ 2`,
and `d ≥ 1024 C (8N)^{1/m} log(8MN)`, every single-pass streaming algorithm with `B` bits of
memory that solves the NGCA testing problem 1.2 with `N` samples has `B ≥ c · d² / (C² N^{2/m})`. -/
theorem theorem_1_4.{u} : ∃ c : ℝ, 0 < c ∧
    ∀ (d N m : ℕ) (C M : ℝ) (A : Measure ℝ) [IsProbabilityMeasure A],
      1 ≤ N → 2 ≤ m → 2 ≤ C → AssumptionA1 M A → AssumptionA2 C m A →
      1024 * C * ((8 * N : ℕ) : ℝ) ^ ((1 : ℝ) / m) * Real.log (8 * M * N) ≤ (d : ℝ) →
      ∀ (B : ℕ) (Ω : Type u) [MeasurableSpace Ω] (alg : StreamingAlg B (Rd d) Ω),
        alg.Solves N (gammaD d) (ngcaAlternatives d A) →
        c * (d : ℝ) ^ 2 / (C ^ 2 * (N : ℝ) ^ ((2 : ℝ) / m)) ≤ (B : ℝ) := by sorry

end MemSampleNGCA.Main
