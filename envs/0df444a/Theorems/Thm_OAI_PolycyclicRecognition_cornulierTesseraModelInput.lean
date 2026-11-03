-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_cornulierTesseraModelInput
-- name    : OAI.PolycyclicRecognition.cornulierTesseraModelInput
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:44:39.008171+00:00
-- url     : https://prove2.me/theorems/7d6dc06c-5813-43af-93a4-f02715d7cd93
-- title:
--   OAI.PolycyclicRecognition.cornulierTesseraModelInput: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.cornulierTesseraModelInput` of [lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/CornulierTesseraConstruction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/CornulierTesseraConstruction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped Manifold`):
--
--   ```lean
--   theorem cornulierTesseraModelInput : CornulierTesseraModelInput
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.CornulierTesseraModelInput` (definitions bundle `OAIQ093D009` of this split).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.group_recognition_of_gromov` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/CornulierTesseraConstruction.lean (declaration OAI.PolycyclicRecognition.cornulierTesseraModelInput)

import Mathlib
import Definitions.Def_OAIQ093D009

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance] semidirectProductTopology

theorem cornulierTesseraModelInput : CornulierTesseraModelInput := by
  sorry

end PolycyclicRecognition

end

end OAI
end
