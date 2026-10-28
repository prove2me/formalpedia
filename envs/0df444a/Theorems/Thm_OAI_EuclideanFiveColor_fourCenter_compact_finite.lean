-- Prove2me | Theorems.Thm_OAI_EuclideanFiveColor_fourCenter_compact_finite
-- name    : OAI.EuclideanFiveColor.fourCenter_compact_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T12:51:36.941989+00:00
-- url     : https://prove2.me/theorems/0246acd4-7e22-4673-81c4-e51b605e4525
-- title:
--   OAI.EuclideanFiveColor.fourCenter_compact_finite: intermediate lemma from OpenAI, The Euclidean plane cannot be colored with five colors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EuclideanFiveColor.no_proper_five_coloring`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Euclidean plane cannot be colored with five colors*, OpenAI Math Release, September 23, 2026, result family 158, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EuclideanFiveColor.fourCenter_compact_finite` of [lean/OAI/Geometry/PlaneColoring/PlaneColoring/Accumulation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneColoring/Accumulation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EuclideanFiveColor`, with `open Set Filter Topology MeasureTheory`):
--
--   ```lean
--   lemma fourCenter_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
--       (K∩{x | FourCenter c x}).Finite
--   ```
--
--   **Definitions.** The statement is written with `OAI.EuclideanFiveColor.FourCenter` (definitions bundle `OAIQ5T4000` of this split); `OAI.EuclideanFiveColor.WeakColoring` (definitions bundle `OAIQ5T4002` of this split).
--
--   **Used by.** The proof of `OAI.EuclideanFiveColor.fullApprox_exists` of this split imports it.
-- source:
--   OpenAI, The Euclidean plane cannot be colored with five colors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 158; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-plane-is-not-five-colorable-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PlaneColoring/PlaneColoring/Accumulation.lean (declaration OAI.EuclideanFiveColor.fourCenter_compact_finite)

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
variable (c : ℂ → Fin 5) (hc : Measurable c)
include hc
lemma fourCenter_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩{x | FourCenter c x}).Finite := by
  sorry

end EuclideanFiveColor

end

end OAI
end
