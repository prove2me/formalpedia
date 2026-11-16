-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_Supplement_theorem_1_2
-- name    : MemOracleLB.Optimization.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:35.524429+00:00
-- url     : https://prove2.me/theorems/2641a66a-4100-4f5f-b0f6-576513e07bdc
-- title:
--   Theorem 1.2 — Uniform sampling lower bound
-- statement:
--   Let $\mathcal C_n$ be the class of convex bodies $K\subseteq\mathbb R^n$ satisfying $B^n\subseteq K\subseteq Cn^{3/2}B^n$, where $B^n$ is the closed Euclidean unit ball. There are absolute constants $a>0$, $C_0\ge1$ and $N\ge2$ such that the following holds for every $C\ge C_0$ and $n\ge N$. Let $S$ be any adaptive randomized membership sampler with arbitrary internal probability space. Suppose its output law $Q_{S,K}$ satisfies
--   $$\sup_{E\text{ measurable}}|Q_{S,K}(E)-U_K(E)|\le\frac1{10}\qquad(K\in\mathcal C_n),$$
--   where $U_K$ is normalized volume on $K$. Then for some $K\in\mathcal C_n$, writing $T_K$ for its query count,
--   $$\mathbb P\!\left(T_K\ge a\frac{n^2}{(\log n)^2}\right)\ge\frac1{100},\qquad
--   \mathbb E T_K\ge a\frac{n^2}{(\log n)^2}.$$
--
--   The constants are independent of the sampler, its seed space, $C$ and $n$. A non-halting run has infinite query count and no output; its missing output mass is included in the total variation error. This companion theorem gives the paper's sampling lower bound alongside the mission's optimization goal; it is not used in the proof of that goal.
--
--   Differences from the source:
--   - reading: a sufficiently large universal class constant C → every C ≥ C₀, with the lower-bound constant and dimension threshold uniform in C; reason: the larger class contains the fixed hard bodies; this is the reading prescribed for the published goal
--   - generalization: Theorem 1.2 states the expectation lower bound → the expectation and the probability-1/100 tail bound hold on the same body with one positive constant a; reason: the paragraph after Corollary 1.3 on PDF p. 3 states this tail guarantee, and the joint proof on PDF p. 21 concludes both; decrease a to share it
--   - encoding: a randomized algorithm and its output distribution → an arbitrary probability seed space with adaptive point-valued actions measurable separately at each finite history; output is a sub-probability law with missing non-halting mass; reason: the source probabilities require seed measurability; disjoint halting-leaf pushforwards retain every output and count non-halting mass against the TV tolerance without an extra halting assumption
--   - encoding: Ω(n²/log² n) for sufficiently large dimension → positive universal a and threshold N ≥ 2, query counts in ℕ∞ and expectations in ℝ≥0∞; reason: explicit asymptotic quantifiers and nonnegative extended expectations preserve infinite runs and avoid undefined logarithmic boundary cases
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Theorem 1.2, PDF p. 3 (printed p. 2); proof PDF p. 21 (printed p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Supplement_Sampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal
universe u1_2
noncomputable section

namespace MemOracleLB.Optimization.Supplement

/-- Theorem 1.2, PDF p.3, with the tail guarantee stated on the same page.
The class constant is read uniformly over every sufficiently large C. -/
theorem theorem_1_2 :
    ∃ a C₀ : ℝ, 0 < a ∧ 1 ≤ C₀ ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, N ≤ n →
    ∀ (Ω : Type u1_2) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (S : SamplingAlgorithm n Ω),
      (∀ K : Set (E n), InClass C K →
        totalVariation (outputLaw S K P) (uniformLaw K) ≤ (1 / 10 : ℝ≥0∞)) →
      ∃ K : Set (E n), InClass C K ∧
        (1 / 100 : ℝ≥0∞) ≤ P {ω |
          ENNReal.ofReal (a * (n : ℝ) ^ 2 / (Real.log n) ^ 2) ≤
            (samplingQueries S K ω).toENNReal} ∧
        ENNReal.ofReal (a * (n : ℝ) ^ 2 / (Real.log n) ^ 2) ≤
          ∫⁻ ω, (samplingQueries S K ω).toENNReal ∂P := by sorry

end MemOracleLB.Optimization.Supplement
