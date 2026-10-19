-- Prove2me | Theorems.Thm_OAI_CriticalSK_partial_sum_maximal_tail
-- name    : OAI.CriticalSK.partial_sum_maximal_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T21:35:24.781673+00:00
-- url     : https://prove2.me/theorems/3f78ddf7-a3a4-4544-aefa-cedb8399ceb2
-- title:
--   Maximal Hoeffding inequality: P(max_{k ≤ m} S_k ≥ a) ≤ exp(−a²/(2(m+1)c)) for independent centred c-subgaussian summands
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\Omega$ (`[IsProbabilityMeasure μ]`). Let $X_0, X_1, \dots : \Omega \to \mathbb{R}$ be random variables (`X : ℕ → Ω → ℝ`) with the following properties:
--   - each is strongly measurable (`hX`);
--   - they are mutually independent (`hind : iIndepFun X μ`);
--   - each has mean zero (`hmean`);
--   - each is subgaussian with variance proxy $c > 0$ in Mathlib's sense, $\mathbb{E}\,e^{tX_i} \le e^{c t^2/2}$ for all real $t$ (`hmgf : ∀ i, HasSubgaussianMGF (X i) c μ` with `c : ℝ≥0` and `hc : 0 < c`).
--
--   Write $S_k = X_0 + \dots + X_k$. Then for every $m \in \mathbb{N}$ and every $a \ge 0$ (`ha`),
--   $$\mu\Bigl(\exists\, k \le m,\ a \le S_k\Bigr) \;\le\; \exp\Bigl(-\frac{a^2}{2(m+1)c}\Bigr).$$
--   The left side is written `μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω}`.
--
--   This is the maximal form of Hoeffding's inequality for subgaussian summands. The bound for the single sum $S_m$ is Hoeffding's (1963). The same bound holds for the maximum of the partial sums because $e^{tS_k}$ is a submartingale, so Doob's maximal inequality applies.
--
--   Lean: `OAI.CriticalSK.partial_sum_maximal_tail`, OpenAI's lemma of that name in `lean/OAI/MathematicalPhysics/CriticalSK/GaussianConcentration.lean`. The statement uses only Mathlib.
-- source:
--   W. Hoeffding, Probability inequalities for sums of bounded random variables, J. Amer. Statist. Assoc. 58 (1963), 13–30 (the maximal form of Hoeffding's inequality, via J. L. Doob's maximal inequality for submartingales). Lean proof: OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/GaussianConcentration.lean (declaration OAI.CriticalSK.partial_sum_maximal_tail)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma partial_sum_maximal_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  sorry

end

end CriticalSK

end

end OAI
end
