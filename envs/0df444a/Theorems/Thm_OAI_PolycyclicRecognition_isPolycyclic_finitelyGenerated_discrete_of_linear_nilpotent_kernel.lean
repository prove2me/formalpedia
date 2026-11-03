-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
-- name    : OAI.PolycyclicRecognition.isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:05:42.19422+00:00
-- url     : https://prove2.me/theorems/ad1e7454-69ac-4ca4-a1c6-47816c5143fb
-- title:
--   OAI.PolycyclicRecognition.isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel` of [lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/DiscreteLinearNilpotentKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/DiscreteLinearNilpotentKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped Manifold`):
--
--   ```lean
--   theorem isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
--       (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : LieRing.IsNilpotent I)
--       (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
--       (hker : LinearMap.ker d = I.toSubmodule)
--       (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
--       (π : G →* Multiplicative W) (hπ : Continuous π)
--       (he : ∀ x, (π (Exp x)).toAdd = d x)
--       (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.IsGroupExponential` and `OAI.PolycyclicRecognition.IsPolycyclic` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.group_recognition_of_gromov` and `OAI.PolycyclicRecognition.lattice_recognition` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/DiscreteLinearNilpotentKernel.lean (declaration OAI.PolycyclicRecognition.isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel)

import Mathlib
import Definitions.Def_PolycyclicRecognition

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : LieRing.IsNilpotent I)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (hker : LinearMap.ker d = I.toSubmodule)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (he : ∀ x, (π (Exp x)).toAdd = d x)
    (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ := by
  sorry

end PolycyclicRecognition

end

end OAI
end
