-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_profile_endpoint_lifts
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_profile_endpoint_lifts
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-02T19:48:33.536535+00:00
-- url     : https://prove2.me/theorems/3f29635c-bc54-43eb-937e-e80f7b2ef033
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_profile_endpoint_lifts: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_profile_endpoint_lifts` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanProfileEndpointLifts.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanProfileEndpointLifts.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Metric Set Filter`, `open scoped Manifold Pointwise Topology`):
--
--   ```lean
--   theorem exists_sequence_profile_endpoint_lifts
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ₀ : M.Bases)
--       (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
--         (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
--         (cartanLog H F.D.equiv F.ExpD
--           (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {K : ℝ} (hK : 0 ≤ K)
--       (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
--       {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
--       (β : M.Bases)
--       (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW E) β.val)
--       (scale η : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
--       (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
--       (hη : Tendsto η atTop (𝓝 0))
--       (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
--       ∃ RN RD : ℕ → ℝ, (∀ n, 0 ≤ RN n) ∧ (∀ n, 0 ≤ RD n) ∧
--         HasSubexponentialUpperBoundSeq scale RN ∧ HasSubexponentialUpperBoundSeq scale RD ∧
--         ∀ n {g : G} (γ : Path (1 : G) g),
--           PathMetricBound γ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
--           (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
--             2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
--           ∃ (u : F.N.carrier) (d : F.D.carrier),
--             F.inclusionN u * F.inclusionD d = g ∧
--             (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
--             u ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
--               E β (scale n) (RN n) ∧
--             ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
--               (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
--               d)‖ ≤ RD n
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.PathMetricBound` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost` and `OAI.PolycyclicRecognition.CartanWordModel.groupBox` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts` and `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_profile_bridge_restrictions_of_basis` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanProfileEndpointLifts.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_profile_endpoint_lifts)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Pointwise Topology

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hπExp hchartN hchartD dynkinN dynkinD in
theorem exists_sequence_profile_endpoint_lifts
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (scale η : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n)
    (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ RN RD : ℕ → ℝ, (∀ n, 0 ≤ RN n) ∧ (∀ n, 0 ≤ RD n) ∧
      HasSubexponentialUpperBoundSeq scale RN ∧ HasSubexponentialUpperBoundSeq scale RD ∧
      ∀ n {g : G} (γ : Path (1 : G) g),
        PathMetricBound γ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
        (∀ t, ∃ z ∈ E, ‖(π (γ t)).toAdd - scale n • z‖ ≤
          2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
        ∃ (u : F.N.carrier) (d : F.D.carrier),
          F.inclusionN u * F.inclusionD d = g ∧
          (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
          u ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
            E β (scale n) (RN n) ∧
          ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
            (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective)
            d)‖ ≤ RD n := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
