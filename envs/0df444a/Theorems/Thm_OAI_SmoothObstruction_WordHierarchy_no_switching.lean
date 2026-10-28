-- Prove2me | Theorems.Thm_OAI_SmoothObstruction_WordHierarchy_no_switching
-- name    : OAI.SmoothObstruction.WordHierarchy.no_switching
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:17:23.157962+00:00
-- url     : https://prove2.me/theorems/086701db-0703-4be5-a24b-e071a1f138cf
-- title:
--   OAI.SmoothObstruction.WordHierarchy.no_switching: intermediate lemma from OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SmoothObstruction.WordHierarchy.no_switching` of [lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/Obstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/Obstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SmoothObstruction.WordHierarchy`, with `open MeasureTheory Set Filter Topology WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw`, `open scoped ENNReal`):
--
--   ```lean
--   theorem no_switching {M : Type} [MetricSpace M] [CompactSpace M]
--       [MeasurableSpace M] [BorelSpace M] [Nonempty M]
--       (μ : Measure Extension) [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
--       (ν : Measure M) [IsProbabilityMeasure ν]
--       (R : M ≃ M) (hR : MeasurePreserving R ν ν) (hRi : MeasurePreserving R.symm ν ν)
--       (r : M → Extension) (hr : MeasurePreserving r ν μ)
--       (B : Set M) (hB : MeasurableSet B) (hBc : ν Bᶜ=0) (hBinv : R.symm ⁻¹' B=B)
--       (hforward : ∀ t,∀ x∈B,r ((R^[t]) x)=(T^[t]) (r x))
--       (hswitch : SmoothSwitching ν R R.symm) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.SmoothObstruction.SmoothSwitching`, `OAI.SmoothObstruction.PhaseDynamics.Space`, `OAI.SmoothObstruction.WordAlphabet.Space`, `OAI.SmoothObstruction.WordHierarchy.A`, `OAI.SmoothObstruction.WordHierarchy.Extension`, `OAI.SmoothObstruction.WordHierarchy.S`, `OAI.SmoothObstruction.WordHierarchy.T` and `OAI.SmoothObstruction.WordParameters.length` (definitions bundle `OAIQ5T3000` of this split).
--
--   **Used by.** The proof of `OAI.SmoothObstruction.main` of this split imports it.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/Obstruction.lean (declaration OAI.SmoothObstruction.WordHierarchy.no_switching)

import Mathlib
import Definitions.Def_OAIQ5T3000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SmoothObstruction.WordHierarchy
open MeasureTheory Set Filter Topology WordParameters WordAlphabet WordStep WordConcatenation FiniteLaw
open scoped ENNReal

theorem no_switching {M : Type} [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M]
    (μ : Measure Extension) [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (ν : Measure M) [IsProbabilityMeasure ν]
    (R : M ≃ M) (hR : MeasurePreserving R ν ν) (hRi : MeasurePreserving R.symm ν ν)
    (r : M → Extension) (hr : MeasurePreserving r ν μ)
    (B : Set M) (hB : MeasurableSet B) (hBc : ν Bᶜ=0) (hBinv : R.symm ⁻¹' B=B)
    (hforward : ∀ t,∀ x∈B,r ((R^[t]) x)=(T^[t]) (r x))
    (hswitch : SmoothSwitching ν R R.symm) : False := by
  sorry
end SmoothObstruction.WordHierarchy

end

end OAI
end
