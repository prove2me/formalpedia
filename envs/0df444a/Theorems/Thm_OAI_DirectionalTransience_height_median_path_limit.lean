-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_height_median_path_limit
-- name    : OAI.DirectionalTransience.height_median_path_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:46:02.330593+00:00
-- url     : https://prove2.me/theorems/a097ada1-228c-4a49-a333-ef5dc629d6c0
-- title:
--   OAI.DirectionalTransience.height_median_path_limit: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.height_median_path_limit` of [lean/OAI/Probability/Ballisticity/Walk/GaussianPathFiniteLawSmul.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Walk/GaussianPathFiniteLawSmul.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Pointwise Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Pointwise Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem height_median_path_limit {Ω : Type*} [MeasurableSpace Ω]
--       (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
--       (hF : ∀ k, Measurable (F k)) (b : ℕ → ℝ)
--       (hb : ∀ k, (1/2 : ℝ≥0∞) ≤ μ {x | F k x ≤ b k} ∧ (1/2 : ℝ≥0∞) ≤ μ {x | b k ≤ F k x})
--       (r n : ℕ → ℝ) (hn : ∀ i, 0 ≤ n i) (hnlim : Tendsto n atTop atTop) (c : ℝ)
--       (hd : ∀ S : ℝ, 0 ≤ S → ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
--         Tendsto (fun i => ((heightPathLaw μ F hF (r i) (n i) S).prod
--           (heightPathLaw μ F hF (r i) (n i) S)).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable) atTop (𝓝 W) ∧
--         ∀ I : Finset unitInterval,
--           (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (S/c) I)
--       {T : ℝ} (hT : 0 ≤ T) :
--       ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
--         TendstoInDistribution (fun i x => heightPolygon (fun k => F k x-b k) (r i) (n i) T)
--           atTop id (fun _ => μ) W ∧
--         ∀ I : Finset unitInterval,
--           (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T/(2*c)) I
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.continuousPathBorelSpace`, `OAI.DirectionalTransience.continuousPathMeasurableSpace`, `OAI.DirectionalTransience.gaussianPathFiniteLaw`, `OAI.DirectionalTransience.heightPathLaw` and `OAI.DirectionalTransience.heightPolygon` (definitions bundle `OAIQ242Bal001` of this split).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.recordMedianSlope_small`, `OAI.DirectionalTransience.shared_median_pair_path_limit` and `OAI.DirectionalTransience.transverse_firstHit_linear_path_limit` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Walk/GaussianPathFiniteLawSmul.lean (declaration OAI.DirectionalTransience.height_median_path_limit)

import Mathlib
import Definitions.Def_OAIQ242Bal001

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem height_median_path_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
    (hF : ∀ k, Measurable (F k)) (b : ℕ → ℝ)
    (hb : ∀ k, (1/2 : ℝ≥0∞) ≤ μ {x | F k x ≤ b k} ∧ (1/2 : ℝ≥0∞) ≤ μ {x | b k ≤ F k x})
    (r n : ℕ → ℝ) (hn : ∀ i, 0 ≤ n i) (hnlim : Tendsto n atTop atTop) (c : ℝ)
    (hd : ∀ S : ℝ, 0 ≤ S → ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      Tendsto (fun i => ((heightPathLaw μ F hF (r i) (n i) S).prod
        (heightPathLaw μ F hF (r i) (n i) S)).map (f := fun pair : C(unitInterval,ℝ) × C(unitInterval,ℝ) => pair.1-pair.2) (continuous_fst.sub continuous_snd).aemeasurable) atTop (𝓝 W) ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (S/c) I)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i x => heightPolygon (fun k => F k x-b k) (r i) (n i) T)
        atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T/(2*c)) I := by
  sorry

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end
