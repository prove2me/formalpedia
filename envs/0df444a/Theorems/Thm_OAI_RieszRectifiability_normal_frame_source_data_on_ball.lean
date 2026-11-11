-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_normal_frame_source_data_on_ball
-- name    : OAI.RieszRectifiability.normal_frame_source_data_on_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:21.326821+00:00
-- url     : https://prove2.me/theorems/0414f6d9-a12e-45f3-a156-302794ac3255
-- title:
--   OAI.RieszRectifiability.normal_frame_source_data_on_ball: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.normal_frame_source_data_on_ball` of [lean/OAI/Analysis/RieszRectifiability/Packing/NormalFrameSourceEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Packing/NormalFrameSourceEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem normal_frame_source_data_on_ball {q d : ℕ} (p : ℕ) (C G : ℝ)
--       (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
--       (hC : 0 < C)
--       (hlower : ∀ j r, AdmissibleRadius (μ j) r →
--         ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball 0 r))
--       (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
--       (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
--       (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
--       (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
--       (hA : Tendsto A atTop atTop)
--       (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
--       (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
--       (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0))
--       (hsource : ∀ i j l, l ≤ T j →
--         (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ j) ≤
--           δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
--       ∀ i : Fin q, ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
--         MemLp (fun x => normalCoordinate (a j) (N j) i x / δ j) 2 ((μ j).restrict (ball 0 r)) ∧
--         (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ j) ^ 2 ∂μ j) ≤ B ∧
--         Integrable (fun v : Ambient d × Ambient d =>
--           fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2)
--           (((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ∧
--         (∫ v : Ambient d × Ambient d,
--           fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2
--             ∂((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ≤ E
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.fractionalPairEnergy` and `OAI.RieszRectifiability.normalCoordinate` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proofs of `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy` and `OAI.RieszRectifiability.exists_dyadic_source_excess_limit` of this split import it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Packing/NormalFrameSourceEnergy.lean (declaration OAI.RieszRectifiability.normal_frame_source_data_on_ball)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem normal_frame_source_data_on_ball {q d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball 0 r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ i j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ j) ≤
        δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∀ i : Fin q, ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
      MemLp (fun x => normalCoordinate (a j) (N j) i x / δ j) 2 ((μ j).restrict (ball 0 r)) ∧
      (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ j) ^ 2 ∂μ j) ≤ B ∧
      Integrable (fun v : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2)
        (((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ∧
      (∫ v : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2
          ∂((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ≤ E := by
  sorry

end

end RieszRectifiability

end OAI
end
