-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_actual_fast_bridge_product
-- name    : OAI.StandardMapEntropy.actual_fast_bridge_product
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:16:05.848981+00:00
-- url     : https://prove2.me/theorems/5ae97a6c-e07c-4743-a758-75d8d3436aa0
-- title:
--   OAI.StandardMapEntropy.actual_fast_bridge_product: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.actual_fast_bridge_product` of [lean/OAI/Dynamics/StandardMap/StandardMap/FastBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/FastBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology Classical`):
--
--   ```lean
--   lemma actual_fast_bridge_product (k : ℝ) (hc : BridgeScalarControl k)
--       (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
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
--       (∫⁻ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
--         ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤
--         fastBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
--           ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
--             area {z | h/2 < shortfallObservation k ah nh Fh z}
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.BridgeScalarControl`, `OAI.StandardMapEntropy.fastBridgeConstant`, `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.shortfallObservation` and `OAI.StandardMapEntropy.torusFastBridge` (definitions bundle `OAIQ2St000` of this split); `OAI.StandardMapEntropy.Circle`, `OAI.StandardMapEntropy.Torus` and `OAI.StandardMapEntropy.area` (the published bundle `Def_StandardMapEntropy`).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected` and `OAI.StandardMapEntropy.CriticalScaleSequence.weight_middle_null` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/FastBridge.lean (declaration OAI.StandardMapEntropy.actual_fast_bridge_product)

import Mathlib
import Definitions.Def_StandardMapEntropy
import Definitions.Def_OAIQ2St000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma actual_fast_bridge_product (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
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
    (∫⁻ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area) ≤
      fastBridgeConstant*((∫⁻ z, ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+
        ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*
          area {z | h/2 < shortfallObservation k ah nh Fh z} := by
  sorry
end StandardMapEntropy

end OAI
end
