-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_gaussian_renewal_path_limit
-- name    : OAI.DirectionalTransience.gaussian_renewal_path_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:36.801611+00:00
-- url     : https://prove2.me/theorems/5352ce3f-c206-48ff-baae-2670370a2be3
-- title:
--   OAI.DirectionalTransience.gaussian_renewal_path_limit: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.gaussian_renewal_path_limit` of [lean/OAI/Probability/Ballisticity/Estimates/CommonWidthProcess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/CommonWidthProcess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology`):
--
--   ```lean
--   theorem gaussian_renewal_path_limit {Ω : Type*} [MeasurableSpace Ω]
--       (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
--       (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
--       (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
--       (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
--       (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
--       (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
--       (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
--       (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
--         atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
--       {T : ℝ} (hT : 0 ≤ T) :
--       ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
--         TendstoInDistribution (fun i ω => scaledPolygon
--           (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω))
--           (r i) (fluctuationScale μ (X 0) (r i)) T) atTop id (fun _ => μ) W ∧
--         ∀ I : Finset unitInterval,
--           (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
--             gaussianPathFiniteLaw (T/c) I
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.fluctuationScale` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.continuousPathBorelSpace`, `OAI.DirectionalTransience.continuousPathMeasurableSpace`, `OAI.DirectionalTransience.gaussianPathFiniteLaw`, `OAI.DirectionalTransience.renewalRewardIncrement`, `OAI.DirectionalTransience.renewalSum` and `OAI.DirectionalTransience.scaledPolygon` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.IsGaussianSequence` (definitions bundle `OAIQ242Bal002` of this split).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.transverse_firstHit_path_limit` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/CommonWidthProcess.lean (declaration OAI.DirectionalTransience.gaussian_renewal_path_limit)

import Mathlib
import Definitions.Def_OAIQ242Bal002

section

attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

theorem gaussian_renewal_path_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {ω | X 0 ω ≠ 0})
    (L : ℕ → Ω → ℕ) (hL : ∀ k, Measurable (L k))
    (hpos : ∀ᵐ ω ∂μ, ∀ k, 0 < L k ω) {c : ℝ} (hc : 1 ≤ c)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun k : ℕ => (renewalSum (fun j => L j ω) k : ℝ)/k)
      atTop (𝓝 c)) (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i ω => scaledPolygon
        (renewalRewardIncrement (fun k => X k ω) (fun k => L k ω))
        (r i) (fluctuationScale μ (X 0) (r i)) T) atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun f : C(unitInterval,ℝ) => I.restrict f) =
          gaussianPathFiniteLaw (T/c) I := by
  sorry

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end
