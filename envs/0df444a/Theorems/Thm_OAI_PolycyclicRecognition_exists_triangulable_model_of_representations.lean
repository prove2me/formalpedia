-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_exists_triangulable_model_of_representations
-- name    : OAI.PolycyclicRecognition.exists_triangulable_model_of_representations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:26:33.677763+00:00
-- url     : https://prove2.me/theorems/a02c3d49-9326-4507-96b7-0b6ddbef4c42
-- title:
--   OAI.PolycyclicRecognition.exists_triangulable_model_of_representations: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.exists_triangulable_model_of_representations` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RepresentedSolvableLieModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RepresentedSolvableLieModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped Manifold Matrix.Norms.Operator`):
--
--   ```lean
--   theorem exists_triangulable_model_of_representations
--       {X : Type} [Group X] [TopologicalSpace X] (f : ProperCocompactHom G X)
--       (hrep : ∃ n, ∃ τ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ,
--         Continuous τ ∧ Function.Injective τ ∧
--         (∀ g, (τ g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular) ∧
--         Nonempty (RepresentedLocalChart (E := E) τ)) :
--       ∃ S : SimplyConnectedSolvableLieModel, IsRealTriangulable S ∧
--         Nonempty (ProperCocompactHom S.carrier X)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.IsRealTriangulable`, `OAI.PolycyclicRecognition.ProperCocompactHom` and `OAI.PolycyclicRecognition.RepresentedLocalChart` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.SimplyConnectedSolvableLieModel` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.ComplexWeightFactorModel.exists_triangulable_rotation_model` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/RepresentedSolvableLieModel.lean (declaration OAI.PolycyclicRecognition.exists_triangulable_model_of_representations)

import Mathlib
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
open scoped Manifold Matrix.Norms.Operator

variable {G E : Type} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [SimplyConnectedSpace G] [Group.IsSolvable G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} {ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ}

theorem exists_triangulable_model_of_representations
    {X : Type} [Group X] [TopologicalSpace X] (f : ProperCocompactHom G X)
    (hrep : ∃ n, ∃ τ : G →* (Matrix (Fin n) (Fin n) ℝ)ˣ,
      Continuous τ ∧ Function.Injective τ ∧
      (∀ g, (τ g : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular) ∧
      Nonempty (RepresentedLocalChart (E := E) τ)) :
    ∃ S : SimplyConnectedSolvableLieModel, IsRealTriangulable S ∧
      Nonempty (ProperCocompactHom S.carrier X) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
