-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_virtuallyPolycyclic_of_coarse_rational_bounds
-- name    : OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:27:22.787293+00:00
-- url     : https://prove2.me/theorems/4d523853-0860-4824-adde-e30985e01a62
-- title:
--   OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds` of [lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/RationalRecognitionEndgame.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/RationalRecognitionEndgame.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open CategoryTheory`):
--
--   ```lean
--   theorem virtuallyPolycyclic_of_coarse_rational_bounds
--       (e : GroupCoarseEquivalence P G) (hP : IsVirtuallyPolycyclic P)
--       (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
--       (hb : HasBoundedFiniteSubgroupOrders G)
--       (hs : ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H) :
--       IsVirtuallyPolycyclic G
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.HasBoundedFiniteSubgroupOrders` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.GroupCoarseEquivalence` and `OAI.PolycyclicRecognition.IsVirtuallyPolycyclic` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/RationalRecognitionEndgame.lean (declaration OAI.PolycyclicRecognition.virtuallyPolycyclic_of_coarse_rational_bounds)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {P G : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]

theorem virtuallyPolycyclic_of_coarse_rational_bounds
    (e : GroupCoarseEquivalence P G) (hP : IsVirtuallyPolycyclic P)
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hs : ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H) :
    IsVirtuallyPolycyclic G := by
  sorry

end PolycyclicRecognition

end

end OAI
end
