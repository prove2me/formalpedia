-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_TypeFPInfinity_heightKernel_virtualSolvable
-- name    : OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:22:33.971833+00:00
-- url     : https://prove2.me/theorems/0f648cbb-f7d5-439d-bb15-dc6c574783aa
-- title:
--   OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/HeightKernelVirtualSolvable.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/HeightKernelVirtualSolvable.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open CategoryTheory ThompsonNonamenability`, `open scoped IsMulCommutative`):
--
--   ```lean
--   theorem TypeFPInfinity.heightKernel_virtualSolvable
--       (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
--       [IsMulCommutative (G ⧸ N)]
--       (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
--       (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
--       ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.HasFiniteIntegralCohomologicalDimension`, `OAI.PolycyclicRecognition.TypeFPInfinity` and `OAI.ThompsonNonamenability.InvariantMean` (definitions bundle `OAIQ093D003` of this split).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/HeightKernelVirtualSolvable.lean (declaration OAI.PolycyclicRecognition.TypeFPInfinity.heightKernel_virtualSolvable)

import Mathlib
import Definitions.Def_OAIQ093D003

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]

theorem TypeFPInfinity.heightKernel_virtualSolvable
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  sorry

end PolycyclicRecognition

end

end OAI
end
