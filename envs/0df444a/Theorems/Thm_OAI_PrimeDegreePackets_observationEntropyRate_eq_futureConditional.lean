-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_observationEntropyRate_eq_futureConditional
-- name    : OAI.PrimeDegreePackets.observationEntropyRate_eq_futureConditional
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:45:53.116543+00:00
-- url     : https://prove2.me/theorems/c10f0bc1-c700-4268-a314-2babf7afd240
-- title:
--   OAI.PrimeDegreePackets.observationEntropyRate_eq_futureConditional: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.observationEntropyRate_eq_futureConditional` of [lean/OAI/NumberTheory/PrimePackets/FutureConditionalEntropy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/FutureConditionalEntropy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open MeasureTheory Set`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem observationEntropyRate_eq_futureConditional
--       (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
--       (hT : MeasurePreserving T μ μ) (P : Y → α)
--       (hP : ∀ a, MeasurableSet {y | P y = a}) :
--       observationEntropyRate μ T P =
--         conditionalSigmaEntropy μ P (⨆ n, observationSigma (futureName T P n))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.observationEntropyRate` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.observationSigma` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.conditionalSigmaEntropy` and `OAI.PrimeDegreePackets.futureName` (definitions bundle `OAIQ244Duke024` of this split).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/FutureConditionalEntropy.lean (declaration OAI.PrimeDegreePackets.observationEntropyRate_eq_futureConditional)

import Mathlib
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.xMetrizable _root_.OAI.PrimeDegreePackets.xT2Space _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.finiteIdeleGroupT2Space _root_.ideleGroupT2Space _root_.infiniteAdeleRingT2Space _root_.infiniteIdeleGroupT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal

namespace PrimeDegreePackets

variable {Y α : Type*} [MeasurableSpace Y] [Fintype α]

theorem observationEntropyRate_eq_futureConditional
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ T P =
      conditionalSigmaEntropy μ P (⨆ n, observationSigma (futureName T P n)) := by
  sorry

end PrimeDegreePackets

end

end OAI
end
