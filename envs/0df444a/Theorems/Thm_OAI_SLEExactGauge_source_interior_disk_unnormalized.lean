-- Prove2me | Theorems.Thm_OAI_SLEExactGauge_source_interior_disk_unnormalized
-- name    : OAI.SLEExactGauge.source_interior_disk_unnormalized
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T22:33:36.912925+00:00
-- url     : https://prove2.me/theorems/2ad0e2e9-d9aa-43ae-9ee1-ca125121c663
-- title:
--   OAI.SLEExactGauge.source_interior_disk_unnormalized: intermediate lemma from OpenAI, An explicit exact Hausdorff gauge for SLE
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SLEExactGauge.sourceLowerMain_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit exact Hausdorff gauge for SLE*, OpenAI Math Release, September 26, 2026, result family 230, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SLEExactGauge.source_interior_disk_unnormalized` of [lean/OAI/Probability/SLE/InteriorDiskProof.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SLE/InteriorDiskProof.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SLEExactGauge`, with `open Set Filter MeasureTheory ProbabilityTheory Complex`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   lemma source_interior_disk_unnormalized (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
--     ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
--     ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
--     ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
--       ∀ F : ℂ → ℂ,
--       DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
--       ∀ (q : ℂ) (r : ℝ), 0 < r →
--       ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
--       η 0 = 0 → F (η T) = q →
--       (∀ t ∈ Ioc 0 T, 0 < (η t).im) →
--       (∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r) →
--       ∀ L : ℝ, 1 ≤ L →
--         P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
--           0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤
--           ENNReal.ofReal (C*L^(-c))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SLEExactGauge.IsOrdinaryChordalSLE`, `OAI.SLEExactGauge.survivingDomain` and `OAI.SLEExactGauge.upperHalfPlane` (the published bundle `Def_SLELowerPositivity`).
--
--   **Used by.** The proof of `OAI.SLEExactGauge.source_mesh_parameters` of this split imports it.
-- source:
--   OpenAI, An explicit exact Hausdorff gauge for SLE, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 230; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SLE/InteriorDiskProof.lean (declaration OAI.SLEExactGauge.source_interior_disk_unnormalized)

import Mathlib
import Definitions.Def_SLELowerPositivity

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_interior_disk_unnormalized (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ F : ℂ → ℂ,
    DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → F (η T) = q →
    (∀ t ∈ Ioc 0 T, 0 < (η t).im) →
    (∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤
        ENNReal.ofReal (C*L^(-c)) := by
  sorry
end SLEExactGauge
end

end OAI
end
