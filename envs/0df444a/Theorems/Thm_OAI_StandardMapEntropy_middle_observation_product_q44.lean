-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_middle_observation_product_q44
-- name    : OAI.StandardMapEntropy.middle_observation_product_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:15:00.957093+00:00
-- url     : https://prove2.me/theorems/b68d81ac-3b51-42e3-b898-d764e169425d
-- title:
--   OAI.StandardMapEntropy.middle_observation_product_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.middle_observation_product` of [lean/OAI/Dynamics/StandardMap/StandardMap/MiddleObservationBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/MiddleObservationBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology`):
--
--   ```lean
--   lemma middle_observation_product_q44 (k : ℝ) (hc : BridgeScalarControl k)
--       (N r i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
--       {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
--       (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
--       (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
--       (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
--       (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
--       (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
--       (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
--       (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
--       (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
--       (h : ℝ) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
--       (∫⁻ z in (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩
--         {z | h < shortfallObservation k ah nh Fh z},
--         ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤ middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
--           ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
--             area {z | h/2 < shortfallObservation k ah nh Fh z}
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.BridgeScalarControl`, `OAI.StandardMapEntropy.growthBase` and `OAI.StandardMapEntropy.torusIter` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.bridgeMiddle` and `OAI.StandardMapEntropy.middleBridgeConstant` (definitions bundle `OAIQ44C001` of this split); `OAI.StandardMapEntropy.middlePrefixEvent` and `OAI.StandardMapEntropy.shortfallObservation` (definitions bundle `OAIQ44C002` of this split); `OAI.StandardMapEntropy.Circle`, `OAI.StandardMapEntropy.Torus` and `OAI.StandardMapEntropy.area` (the published bundle `Def_StandardMapComponents`).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/MiddleObservationBridge.lean (declaration OAI.StandardMapEntropy.middle_observation_product)

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002

section

attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma middle_observation_product_q44 (k : ℝ) (hc : BridgeScalarControl k)
    (N r i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫⁻ z in (torusIter k (i:ℤ) ⁻¹' middlePrefixEvent k (N-i) i) ∩
      {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤ middleBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  sorry
end StandardMapEntropy

end OAI
end
