-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_exponentialLinearRealizationInput_intrinsic
-- name    : OAI.PolycyclicRecognition.exponentialLinearRealizationInput_intrinsic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:48:14.164997+00:00
-- url     : https://prove2.me/theorems/f378f66a-bc93-4083-95c9-8f36457e6dc8
-- title:
--   OAI.PolycyclicRecognition.exponentialLinearRealizationInput_intrinsic: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.exponentialLinearRealizationInput_intrinsic` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/IntrinsicTriangularRealization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/IntrinsicTriangularRealization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped Manifold Matrix.Norms.Operator`):
--
--   ```lean
--   theorem exponentialLinearRealizationInput_intrinsic :
--       ExponentialLinearRealizationInput (EG := E) (G := G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` (definitions bundle `OAIQ093D008` of this split).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.CartanWordModel.exists_cover_metric_action_box_bound`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_height_intrinsic`, `OAI.PolycyclicRecognition.cartan_cover_controlled_pairs`, `OAI.PolycyclicRecognition.cartan_unitary_reduced_vanishing` and `OAI_PolycyclicRecognition_exists_semidirect_box_metric_bound` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/IntrinsicTriangularRealization.lean (declaration OAI.PolycyclicRecognition.exponentialLinearRealizationInput_intrinsic)

import Mathlib
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem exponentialLinearRealizationInput_intrinsic :
    ExponentialLinearRealizationInput (EG := E) (G := G) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
