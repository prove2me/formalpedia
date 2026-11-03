-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_segmentWordPath_bound
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:35:42.244403+00:00
-- url     : https://prove2.me/theorems/1f497722-ab53-4bf3-b5fd-f525e829790b
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSegmentWordPath.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSegmentWordPath.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule`, `open scoped Manifold`):
--
--   ```lean
--   theorem exists_segmentWordPath_bound [IsIsometricSMul G G]
--       {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
--       (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
--       {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
--       (v : H) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
--         ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N → (∀ z ∈ u, |z.2| ≤ B) →
--         PathMetricBound (M.segmentWordPath T hExp realize v r u)
--           (C * r) (C * (1 + Real.log (2 + r))) ∧
--         ∀ t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
--           (l (M.segmentWordPath T hExp realize v r u t)).toAdd = r • z
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.CartanWordModel` and `OAI.PolycyclicRecognition.cartanRootIdeal` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.PathMetricBound` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.CartanWordModel.segmentScaledWord` and `OAI.PolycyclicRecognition.CartanWordModel.segmentWordPath` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.IsGroupExponential` and `OAI.PolycyclicRecognition.TriangularAdjoint` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.segmentSupport_le_of_stationary_mean` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSegmentWordPath.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_segmentWordPath_bound)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))

set_option maxHeartbeats 1000000 in
theorem exists_segmentWordPath_bound [IsIsometricSMul G G]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : H) {B : ℝ} (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ N → (∀ z ∈ u, |z.2| ≤ B) →
      PathMetricBound (M.segmentWordPath T hExp realize v r u)
        (C * r) (C * (1 + Real.log (2 + r))) ∧
      ∀ t, ∃ z ∈ segment ℝ (0 : W) (l (Exp v)).toAdd,
        (l (M.segmentWordPath T hExp realize v r u t)).toAdd = r • z := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
