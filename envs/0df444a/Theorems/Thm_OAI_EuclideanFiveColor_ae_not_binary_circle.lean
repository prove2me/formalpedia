-- Prove2me | Theorems.Thm_OAI_EuclideanFiveColor_ae_not_binary_circle
-- name    : OAI.EuclideanFiveColor.ae_not_binary_circle
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:48:08.202039+00:00
-- url     : https://prove2.me/theorems/574ad148-f7e4-486e-b8d4-d5a5469ea5f5
-- title:
--   OAI.EuclideanFiveColor.ae_not_binary_circle: intermediate lemma from OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EuclideanFiveColor.ae_not_binary_circle` of [lean/OAI/Geometry/PlaneColoring/PlaneColoring/BinaryPalettes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneColoring/BinaryPalettes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EuclideanFiveColor`, with `open Set Filter Topology MeasureTheory`):
--
--   ```lean
--   lemma ae_not_binary_circle {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
--       (x : ℂ) (i j : Fin k) : ∀ᵐ t ∂angularMeasure, ¬ BinaryCenter c hc (x+direction t) i j
--   ```
--
--   **Definitions.** The statement is written with `OAI.EuclideanFiveColor.Angles`, `OAI.EuclideanFiveColor.BinaryCenter`, `OAI.EuclideanFiveColor.angularMeasure` and `OAI.EuclideanFiveColor.direction` (definitions bundle `OAIQ5T4000` of this split); `OAI.EuclideanFiveColor.WeakColoring` (definitions bundle `OAIQ5T4002` of this split).
--
--   **Used by.** The proofs of `OAI.EuclideanFiveColor.annulus_maps_eventually_forest`, `OAI.EuclideanFiveColor.fiveState_diag`, `OAI.EuclideanFiveColor.fourState_group`, `OAI.EuclideanFiveColor.four_weak_limit_identify`, `OAI.EuclideanFiveColor.no_five_commonInterface` and `OAI.EuclideanFiveColor.threeCenter_compact_finite` of this split import it.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneColoring/BinaryPalettes.lean (declaration OAI.EuclideanFiveColor.ae_not_binary_circle)

import Mathlib
import Definitions.Def_OAIQ5T4002

section

attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_not_binary_circle {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℂ) (i j : Fin k) : ∀ᵐ t ∂angularMeasure, ¬ BinaryCenter c hc (x+direction t) i j := by
  sorry
end EuclideanFiveColor
end

end OAI
end
