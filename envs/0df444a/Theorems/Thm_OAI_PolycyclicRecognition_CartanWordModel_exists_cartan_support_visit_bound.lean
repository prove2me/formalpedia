-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_cartan_support_visit_bound
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_cartan_support_visit_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:31:36.884917+00:00
-- url     : https://prove2.me/theorems/524ce40b-69a0-466e-856d-0aa78f7437a4
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_cartan_support_visit_bound: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_cartan_support_visit_bound` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSupportVisits.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSupportVisits.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra`, `open scoped Manifold BigOperators`):
--
--   ```lean
--   theorem exists_cartan_support_visit_bound
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (π : G →* Multiplicative W)
--       (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
--       {E : Set W} (hE : Convex ℝ E) {w₀ : W} (hw₀ : w₀ ∈ E)
--       (w : Fin M.letterCount → W) (hw : ∀ i, w i ∈ E)
--       (s : Fin M.letterCount → ℝ)
--       (hs : ∀ i, cartanHeightWeight T H (M.weight i) (eW.symm (w i)) = s i)
--       {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (h₀ : H),
--         ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
--         (π (Exp h₀)).toAdd = r • w₀ → ∀ (n : G), π n = 1 →
--         ∀ (i : Fin M.letterCount) (b : ℝ), |b| ≤ B * Real.exp (r * s i) →
--         ∃ γ : Path (n * Exp h₀)
--             (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀),
--           PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
--           (∀ t, ∃ z ∈ E, (π (γ t)).toAdd = r • z) ∧
--           γ = cartanSupportVisitPath T M Exp hExp realize eW w₀ (w i) i n h₀ r b
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanHeightWeight`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.PathMetricBound` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.cartanSupportVisitPath` (definitions bundle `OAIQ093D015` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.ideal_fiber_quotient_difference_tendsto_one` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanSupportVisits.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_cartan_support_visit_bound)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D015

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold BigOperators

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
include F in
theorem exists_cartan_support_visit_bound
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {E : Set W} (hE : Convex ℝ E) {w₀ : W} (hw₀ : w₀ ∈ E)
    (w : Fin M.letterCount → W) (hw : ∀ i, w i ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i) (eW.symm (w i)) = s i)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 ≤ r → ∀ (h₀ : H),
      ‖(finBasis ℝ H).equivFun h₀‖ ≤ A * (1 + r) ^ p →
      (π (Exp h₀)).toAdd = r • w₀ → ∀ (n : G), π n = 1 →
      ∀ (i : Fin M.letterCount) (b : ℝ), |b| ≤ B * Real.exp (r * s i) →
      ∃ γ : Path (n * Exp h₀)
          (n * Exp (b • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h₀),
        PathMetricBound γ (C * r) (C * (1 + Real.log (2 + r))) ∧
        (∀ t, ∃ z ∈ E, (π (γ t)).toAdd = r • z) ∧
        γ = cartanSupportVisitPath T M Exp hExp realize eW w₀ (w i) i n h₀ r b := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
