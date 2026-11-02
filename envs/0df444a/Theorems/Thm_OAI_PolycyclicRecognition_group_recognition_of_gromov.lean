-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_group_recognition_of_gromov
-- name    : OAI.PolycyclicRecognition.group_recognition_of_gromov
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:27:53.886463+00:00
-- url     : https://prove2.me/theorems/d6b16032-53ec-4b96-9df9-39e6fd5f8126
-- title:
--   OAI.PolycyclicRecognition.group_recognition_of_gromov: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.group_recognition_of_gromov` of [lean/OAI/GroupTheory/PolycyclicRecognition/RecognitionFromGromov.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/RecognitionFromGromov.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Module LieAlgebra MeasureTheory`, `open scoped Manifold NNReal`):
--
--   ```lean
--   theorem group_recognition_of_gromov
--       (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
--       {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
--       (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
--       IsVirtuallyPolycyclic J ∧
--         ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
--           ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
--             IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.GromovPolynomialGrowthInput` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.GroupCoarseEquivalence`, `OAI.PolycyclicRecognition.IsUniformLattice`, `OAI.PolycyclicRecognition.IsVirtuallyPolycyclic` and `OAI.PolycyclicRecognition.SimplyConnectedSolvableLieModel` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.group_recognition` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/RecognitionFromGromov.lean (declaration OAI.PolycyclicRecognition.group_recognition_of_gromov)

import Mathlib
import Lean.Elab.Tactic.Omega
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
open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

theorem group_recognition_of_gromov
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
    (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
