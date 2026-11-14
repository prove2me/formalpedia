-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_lastActiveObservation_entropy_budget
-- name    : OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:26:27.809333+00:00
-- url     : https://prove2.me/theorems/48d91cd0-5b3a-4f9f-9e98-5c57606c0121
-- title:
--   OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/LastActiveEntropy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/LastActiveEntropy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set MeasureTheory Function`, `open scoped ENNReal`):
--
--   ```lean
--   theorem exists_lastActiveObservation_entropy_budget
--       {Y : Type*} [MeasurableSpace Y] (K : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
--       ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Summable δ ∧ (∑' n, δ n) ≤ ε/4 ∧
--         ∀ (μ : Measure Y) [IsProbabilityMeasure μ] (S : ℕ → Set Y),
--           (∀ n, MeasurableSet (S n)) → (∀ n, μ.real (S n) ≤ δ n) →
--           ∀ B : ∀ n, Y → Fin (K n), (∀ n, Measurable (B n)) →
--             Summable (fun z => Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) ∧
--             (∑' z, Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.lastActiveObservation` (definitions bundle `OAIQ244Duke012` of this split).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_sparse_upperRoot_comparison` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/LastActiveEntropy.lean (declaration OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget)

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Finset.Max
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_OAIQ244Duke012

section

attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace DukePrimeDegree

theorem exists_lastActiveObservation_entropy_budget
    {Y : Type*} [MeasurableSpace Y] (K : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Summable δ ∧ (∑' n, δ n) ≤ ε/4 ∧
      ∀ (μ : Measure Y) [IsProbabilityMeasure μ] (S : ℕ → Set Y),
        (∀ n, MeasurableSet (S n)) → (∀ n, μ.real (S n) ≤ δ n) →
        ∀ B : ∀ n, Y → Fin (K n), (∀ n, Measurable (B n)) →
          Summable (fun z => Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) ∧
          (∑' z, Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) < ε := by
  sorry

end DukePrimeDegree

end

end OAI
end
