-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actual_buffer_excess
-- name    : OAI.DirectionalTransience.actual_buffer_excess
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:49:07.111929+00:00
-- url     : https://prove2.me/theorems/f572bcd6-a8cc-4ba2-955f-e00d969bc82b
-- title:
--   OAI.DirectionalTransience.actual_buffer_excess: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actual_buffer_excess` of [lean/OAI/Probability/Ballisticity/Estimates/BufferExcess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/BufferExcess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter Function`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem actual_buffer_excess {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ (κ : ℝ≥0) (α s g R : ℝ), 0 < κ ∧ κ ≤ 1 ∧ (∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u) ∧ 0 < α ∧ 0 < s ∧
--         0 < g ∧ g ≤ 1 ∧ 1 ≤ R ∧
--         ∀ (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a),
--         let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
--         let root := bufferRootNode e f hef R a x hx
--         let B := bufferTreeSuccess e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
--           (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
--         ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
--           Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
--           (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W ω) ∧
--           (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ 1+(1-Real.exp (-s/4))⁻¹ ∧
--           (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
--             Real.log R+(s*Real.log (1+α)/8)*(n:ℝ)-W ω*(Real.log (1+α)+s*Real.log (1+α)/8) ≤
--             Real.log (bufferCurrentNode e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
--               (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root ω n).radius)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.AdaptedBufferNode`, `OAI.DirectionalTransience.PairAtHeight`, `OAI.DirectionalTransience.positiveBufferPlan` and `OAI.DirectionalTransience.signedCoordinate` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.successes` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.bufferCurrentNode`, `OAI.DirectionalTransience.bufferRootNode`, `OAI.DirectionalTransience.bufferTreeSuccess` and `OAI.DirectionalTransience.positiveBufferPlan_pos` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.actual_outward_log_bound` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/BufferExcess.lean (declaration OAI.DirectionalTransience.actual_buffer_excess)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal003

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem actual_buffer_excess {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ (κ : ℝ≥0) (α s g R : ℝ), 0 < κ ∧ κ ≤ 1 ∧ (∀ᵐ ω ∂environmentLaw ν, ∀ y u, κ ≤ (ω y).1 u) ∧ 0 < α ∧ 0 < s ∧
      0 < g ∧ g ≤ 1 ∧ 1 ≤ R ∧
      ∀ (a : ℝ) (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a),
      let ε := 1-Real.exp (-(s*Real.log (1+α)/8))
      let root := bufferRootNode e f hef R a x hx
      let B := bufferTreeSuccess e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
        (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root
      ∃ W : Environment d → ℝ, Measurable W ∧ (∀ ω, 0 ≤ W ω) ∧
        Integrable (fun ω => Real.exp (W ω)) (environmentLaw ν) ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ, s/4*(n:ℝ)-successes B n ω ≤ W ω) ∧
        (∫ ω, Real.exp (W ω) ∂environmentLaw ν) ≤ 1+(1-Real.exp (-s/4))⁻¹ ∧
        (∀ᵐ ω ∂environmentLaw ν, ∀ n : ℕ,
          Real.log R+(s*Real.log (1+α)/8)*(n:ℝ)-W ω*(Real.log (1+α)+s*Real.log (1+α)/8) ≤
          Real.log (bufferCurrentNode e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ
            (positiveBufferPlan ν e f) (positiveBufferPlan_pos ν e f) root ω n).radius) := by
  sorry
end DirectionalTransience

end

end

end OAI
end
