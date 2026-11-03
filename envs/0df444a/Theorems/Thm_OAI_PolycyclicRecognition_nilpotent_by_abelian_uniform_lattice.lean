-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_nilpotent_by_abelian_uniform_lattice
-- name    : OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:26:51.635132+00:00
-- url     : https://prove2.me/theorems/059bcb36-fef2-4436-ba40-c13e621ecf6e
-- title:
--   OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice` of [lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/NilpotentByAbelianRealization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/NilpotentByAbelianRealization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped IsMulCommutative`):
--
--   ```lean
--   theorem nilpotent_by_abelian_uniform_lattice (hG : IsPolycyclic G)
--       (ht : HasNoNontrivialTorsion G) (N : Subgroup G) [N.Normal]
--       [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)] :
--       ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
--         (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.HasNoNontrivialTorsion` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.IsPolycyclic`, `OAI.PolycyclicRecognition.IsUniformLattice` and `OAI.PolycyclicRecognition.SimplyConnectedSolvableLieModel` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.dekimpeLatticeRealizationInput` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/NilpotentByAbelianRealization.lean (declaration OAI.PolycyclicRecognition.nilpotent_by_abelian_uniform_lattice)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D003

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G]

theorem nilpotent_by_abelian_uniform_lattice (hG : IsPolycyclic G)
    (ht : HasNoNontrivialTorsion G) (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] [IsMulCommutative (G ⧸ N)] :
    ∃ K : Subgroup G, K.FiniteIndex ∧ ∃ (S : SimplyConnectedSolvableLieModel)
      (Λ : Subgroup S.carrier), IsUniformLattice Λ ∧ Nonempty (K ≃* Λ) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
