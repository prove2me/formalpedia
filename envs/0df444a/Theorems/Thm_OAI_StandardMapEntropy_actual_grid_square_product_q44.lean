-- Prove2me | Theorems.Thm_OAI_StandardMapEntropy_actual_grid_square_product_q44
-- name    : OAI.StandardMapEntropy.actual_grid_square_product_q44
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:14:08.836753+00:00
-- url     : https://prove2.me/theorems/62439473-295f-4522-a02f-ff2b913be8fc
-- title:
--   OAI.StandardMapEntropy.actual_grid_square_product_q44: intermediate lemma from OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StandardMapEntropy.actual_grid_square_product` of [lean/OAI/Dynamics/StandardMap/StandardMap/GridBridge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/GridBridge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StandardMapEntropy`, with `open MeasureTheory Set`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set Filter Metric`, `open scoped ENNReal Topology`):
--
--   ```lean
--   lemma actual_grid_square_product_q44 (k : ℝ) (hc : BridgeScalarControl k)
--       (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
--       (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
--       (ix iy : Fin 32)
--       (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
--       (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
--       (hWp : ∀ z w : ℝ × ℝ,
--         dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
--           8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
--       (hHp : ∀ z w : ℝ × ℝ,
--         dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
--           8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
--       bridgeAreaScale *
--         (∫⁻ z in {z : ℝ × ℝ | z ∈ bridgeGridCell ix ×ˢ bridgeGridCell iy ∧
--           prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
--           ENNReal.ofReal (W (liftProjection z))) ≤
--       bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z}
--   ```
--
--   **Definitions.** The statement is written with `OAI.StandardMapEntropy.BridgeScalarControl`, `OAI.StandardMapEntropy.growthBase`, `OAI.StandardMapEntropy.liftIter` and `OAI.StandardMapEntropy.liftProjection` (definitions bundle `OAIQ44C000` of this split); `OAI.StandardMapEntropy.bridgeAreaScale`, `OAI.StandardMapEntropy.bridgeGridCell` and `OAI.StandardMapEntropy.bridgeLocalConstant` (definitions bundle `OAIQ44C001` of this split); `OAI.StandardMapEntropy.prefixEligible` (definitions bundle `OAIQ44C002` of this split); `OAI.StandardMapEntropy.Circle`, `OAI.StandardMapEntropy.Torus` and `OAI.StandardMapEntropy.area` (the published bundle `Def_StandardMapComponents`).
--
--   **Used by.** The proof of `OAI.StandardMapEntropy.middle_observation_product_q44` of this split imports it.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/StandardMap/StandardMap/GridBridge.lean (declaration OAI.StandardMapEntropy.actual_grid_square_product)

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
lemma actual_grid_square_product_q44 (k : ℝ) (hc : BridgeScalarControl k)
    (np nm Bp Bm : ℕ) (hnp : 1 ≤ np) (hnm : 1 ≤ nm)
    (hBp : Bp=np ∨ Bp=np+1) (hBm : Bm=nm ∨ Bm=nm+1) (hBp2 : 2 ≤ Bp) (hBm2 : 2 ≤ Bm)
    (ix iy : Fin 32)
    (W H : Torus → ℝ) (hW : Continuous W) (hH : Continuous H) (hW0 : ∀ z, 0 ≤ W z)
    (h δ : ℝ) (hδ : 0 ≤ δ) (hδh : δ < h/2)
    (hWp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (-(Bm:ℤ)) z) (liftIter k (-(Bm:ℤ)) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bm-1:ℕ)) → |W (liftProjection z)-W (liftProjection w)| ≤ δ)
    (hHp : ∀ z w : ℝ × ℝ,
      dist (liftIter k (Bp:ℤ) z) (liftIter k (Bp:ℤ) w) ≤
        8/growthBase k^((4/5:ℝ)*(Bp-1:ℕ)) → |H (liftProjection z)-H (liftProjection w)| ≤ δ) :
    bridgeAreaScale *
      (∫⁻ z in {z : ℝ × ℝ | z ∈ bridgeGridCell ix ×ˢ bridgeGridCell iy ∧
        prefixEligible k Bp (np+1) z.swap ∧ prefixEligible k Bm (nm+1) z ∧ h < H (liftProjection z)},
        ENNReal.ofReal (W (liftProjection z))) ≤
    bridgeLocalConstant*((∫⁻ z, ENNReal.ofReal (W z) ∂area)+ENNReal.ofReal δ)*area {z | h/2 < H z} := by
  sorry
end StandardMapEntropy

end OAI
end
