-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_trace_ad_eq_zero_of_intrinsic_kernel_haar
-- name    : OAI.PolycyclicRecognition.trace_ad_eq_zero_of_intrinsic_kernel_haar
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:06:15.013352+00:00
-- url     : https://prove2.me/theorems/9c9cd593-816e-48d4-869e-6136d0a6da41
-- title:
--   OAI.PolycyclicRecognition.trace_ad_eq_zero_of_intrinsic_kernel_haar: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.trace_ad_eq_zero_of_intrinsic_kernel_haar` of [lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/IntrinsicTraceFromHaar.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/IntrinsicTraceFromHaar.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Module LieAlgebra MeasureTheory`, `open scoped Manifold Matrix.Norms.Operator`):
--
--   ```lean
--   theorem trace_ad_eq_zero_of_intrinsic_kernel_haar
--       {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
--       (q : HeightSpace T.character ≃ₗ[ℝ] W)
--       (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
--       (π : G →* Multiplicative W) (hπ : Continuous π)
--       (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
--       (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
--       (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : LinearMap.trace ℝ _ (ad ℝ _ x) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.group_recognition_of_gromov` and `OAI.PolycyclicRecognition.main_uniform_bounded_height` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/IntrinsicTraceFromHaar.lean (declaration OAI.PolycyclicRecognition.trace_ad_eq_zero_of_intrinsic_kernel_haar)

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

open Module LieAlgebra MeasureTheory
open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G] [SimplyConnectedSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem trace_ad_eq_zero_of_intrinsic_kernel_haar
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : LinearMap.trace ℝ _ (ad ℝ _ x) = 0 := by
  sorry

end PolycyclicRecognition

end

end OAI
end
