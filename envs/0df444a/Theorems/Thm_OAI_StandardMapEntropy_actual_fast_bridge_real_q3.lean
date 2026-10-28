-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_actual_fast_bridge_real_q3
-- name    : OAI.StandardMapEntropy.actual_fast_bridge_real_q3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T04:48:05.800282+00:00
-- url     : https://prove2.me/theorems/6d8ab4dc-729e-4d17-9daf-b5c49cc21c3c
-- title:
--   OAI.StandardMapEntropy.actual_fast_bridge_real_q3: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_entropy_complete`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.actual_fast_bridge_real` of [lean/OAI/Dynamics/StandardMap/StandardMap/BridgeRealBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BridgeRealBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology Classical`):
--
--   ```lean
--   lemma actual_fast_bridge_real_q3 (k : ℝ) (hc : BridgeScalarControl k)
--       (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
--       {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
--       (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
--       (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
--       (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
--       (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
--       (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
--       (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
--       (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
--       (hH0 : ∀ z, 0 ≤ shortfallObservation k ah nh Fh z)
--       (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
--       (h : ℝ) (hh : 0<h) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
--       (∫ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
--         shortfallObservation k aw nw Fw z ∂area) ≤
--         bridgeRealConstant*((∫ z,shortfallObservation k aw nw Fw z ∂area)+
--           growthBase k^(-(1/10:ℝ)*(N:ℝ)))*((∫ z,shortfallObservation k ah nh Fh z ∂area)/(h/2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.BridgeScalarControl`, `OAI.StandardMapEntropy.bridgeRealConstant`, `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.shortfallObservation` and `OAI.StandardMapEntropy.torusFastBridge` (definitions bundle `OAIQ3St000` of this split); `OAI.StandardMapEntropy.Circle`, `OAI.StandardMapEntropy.Torus` and `OAI.StandardMapEntropy.area` (the published bundle `Def_StandardMapLyapunov`).
--
--   **Used by.** The proofs of `OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected_q3` and `OAI.StandardMapEntropy.CriticalScaleSequence.weight_affine_null_q3` of this split import it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/BridgeRealBound.lean (declaration OAI.StandardMapEntropy.actual_fast_bridge_real)

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000

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
lemma actual_fast_bridge_real_q3 (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hH0 : ∀ z, 0 ≤ shortfallObservation k ah nh Fh z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hh : 0<h) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      shortfallObservation k aw nw Fw z ∂area) ≤
      bridgeRealConstant*((∫ z,shortfallObservation k aw nw Fw z ∂area)+
        growthBase k^(-(1/10:ℝ)*(N:ℝ)))*((∫ z,shortfallObservation k ah nh Fh z ∂area)/(h/2)) := by
  sorry
end StandardMapEntropy

end OAI
end
