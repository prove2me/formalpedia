-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_conditionalSigmaEntropy_heightClip_tendsto
-- name    : OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:38.152868+00:00
-- url     : https://prove2.me/theorems/d96e1cf5-0e2b-4443-9298-bd591aced831
-- title:
--   OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto` of [lean/OAI/NumberTheory/DukePrimeDegree/Entropy/ConditionalInformationClipping.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/ConditionalInformationClipping.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory Set Filter`, `open scoped Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem conditionalSigmaEntropy_heightClip_tendsto
--       (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
--       (μ : Measure Y) [IsFiniteMeasure μ]
--       (Q : Y → ℕ) (hQ : Measurable Q) (hm : m ≤ mY)
--       (hpos : ∀ᵐ y ∂μ,
--         0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y)
--       (hint : Integrable (conditionalInformation μ Q m) μ) :
--       Tendsto (fun N => conditionalSigmaEntropy μ (heightClip Q N) m) atTop
--         (𝓝 (∫ y, conditionalInformation μ Q m y ∂μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.conditionalInformation` and `OAI.DukePrimeDegree.heightClip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.conditionalSigmaEntropy` (definitions bundle `OAIQ244Duke024` of this split).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.positive_root_sum_le_diagonal_entropy` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Entropy/ConditionalInformationClipping.lean (declaration OAI.DukePrimeDegree.conditionalSigmaEntropy_heightClip_tendsto)

import Mathlib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.xMeasurableSpace _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {Y : Type*}

theorem conditionalSigmaEntropy_heightClip_tendsto
    (m : MeasurableSpace Y) [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (Q : Y → ℕ) (hQ : Measurable Q) (hm : m ≤ mY)
    (hpos : ∀ᵐ y ∂μ,
      0 < (μ[({z | Q z = Q y}.indicator (fun _ => (1 : ℝ))) | m]) y)
    (hint : Integrable (conditionalInformation μ Q m) μ) :
    Tendsto (fun N => conditionalSigmaEntropy μ (heightClip Q N) m) atTop
      (𝓝 (∫ y, conditionalInformation μ Q m y ∂μ)) := by
  sorry

end DukePrimeDegree

end

end OAI
end
