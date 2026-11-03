-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_intrinsic_exponential_contMDiff
-- name    : OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:04:32.728821+00:00
-- url     : https://prove2.me/theorems/e676a3c4-3468-4c65-b0d5-05e819125219
-- title:
--   OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/IntrinsicExponentialSmooth.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/IntrinsicExponentialSmooth.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open scoped Manifold ContDiff Matrix.Norms.Operator`):
--
--   ```lean
--   theorem intrinsic_exponential_contMDiff
--       {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
--       (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
--       ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : E => Exp x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.IsGroupExponential` and `OAI.PolycyclicRecognition.TriangularAdjoint` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.ComplexWeightFactorModel.contMDiff_factorParameter` and `OAI.PolycyclicRecognition.exists_intrinsic_smooth_coordinates` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/IntrinsicExponentialSmooth.lean (declaration OAI.PolycyclicRecognition.intrinsic_exponential_contMDiff)

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

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem intrinsic_exponential_contMDiff
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : E => Exp x) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
