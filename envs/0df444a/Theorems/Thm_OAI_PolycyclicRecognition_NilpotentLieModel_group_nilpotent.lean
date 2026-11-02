-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_NilpotentLieModel_group_nilpotent
-- name    : OAI.PolycyclicRecognition.NilpotentLieModel.group_nilpotent
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:23:21.885829+00:00
-- url     : https://prove2.me/theorems/281c1997-26e3-4f6f-aa8d-113761fc12af
-- title:
--   OAI.PolycyclicRecognition.NilpotentLieModel.group_nilpotent: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.NilpotentLieModel.group_nilpotent` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/NilpotentLieGroupNilpotent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/NilpotentLieGroupNilpotent.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped Manifold`):
--
--   ```lean
--   theorem NilpotentLieModel.group_nilpotent
--       {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
--       (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) : Group.IsNilpotent N.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.cartan_cocycle_approximation` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/NilpotentLieGroupNilpotent.lean (declaration OAI.PolycyclicRecognition.NilpotentLieModel.group_nilpotent)

import Mathlib
import Definitions.Def_OAIQ093D001

section

attribute [-instance] _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

theorem NilpotentLieModel.group_nilpotent
    {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) : Group.IsNilpotent N.carrier := by
  sorry

end PolycyclicRecognition

end

end OAI
end
