-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_sequence_path_tuple_lifts
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T17:59:36.919929+00:00
-- url     : https://prove2.me/theorems/48abf491-d75a-4836-b0c9-0bc6f0d4c81f
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPathTupleLifts.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPathTupleLifts.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra Filter Set`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem exists_sequence_path_tuple_lifts
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (π : G →* Multiplicative W)
--       (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ x, chartN x = F.ExpN x)
--       (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
--       (hchartD : ∀ x, chartD x = F.ExpD x)
--       (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {K : ℝ} (hK : 0 ≤ K)
--       (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
--       (h : ℕ) (E : Fin h → Set W) (β : Fin h → M.Bases)
--       (hEc : ∀ i, IsCompact (E i)) (hEn : ∀ i, (E i).Nonempty)
--       (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--         (M.boxCost T hunimod eW (E i)) (β i).val)
--       (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
--       (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
--       (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
--       (s : ℕ → Set (Fin h → G))
--       (path : ∀ (_n : ℕ) (x : Fin h → G) (i : Fin h), Path (1 : G)
--         ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)))
--       (hmetric : ∀ n x, x ∈ s n → ∀ i,
--         PathMetricBound (path n x i) (A * scale n) (B * (1 + Real.log (2 + scale n))))
--       (htemplate : ∀ n x, x ∈ s n → ∀ i t, ∃ z ∈ E i,
--         ‖(π (path n x i t)).toAdd - scale n • z‖ ≤
--           2 * scale n * η n + A * (1 + Real.log (2 + scale n)))
--       (hend : ∀ n x, x ∈ s n → ∀ i : Fin h,
--         ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
--           η n * scale n) :
--       ∃ (RH R : ℕ → ℝ)
--         (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier)),
--         (∀ n, 0 ≤ RH n) ∧ (∀ n, 0 ≤ R n) ∧
--         HasSubexponentialUpperBoundSeq scale RH ∧ HasSubexponentialUpperBoundSeq scale R ∧
--         ∀ n x, x ∈ s n →
--           (∀ i, F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i) ∧
--           (∀ i, ‖(finBasis ℝ H).equivFun
--             (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n) ∧
--           (∀ i, ‖eW (heightProjection T.character
--             (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) :
--               GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ((h : ℝ) * η n) * scale n) ∧
--           (∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
--             M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.PathMetricBound` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.basedTuplePosition` and `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.prefixCoordinateEquiv` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis`, `OAI.PolycyclicRecognition.CartanWordModel.boxCost` and `OAI.PolycyclicRecognition.CartanWordModel.groupBox` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPathTupleLifts.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_sequence_path_tuple_lifts)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D004
import Definitions.Def_OAIQ093D005
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
theorem exists_sequence_path_tuple_lifts
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (h : ℕ) (E : Fin h → Set W) (β : Fin h → M.Bases)
    (hEc : ∀ i, IsCompact (E i)) (hEn : ∀ i, (E i).Nonempty)
    (hβ : ∀ i, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (E i)) (β i).val)
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 1 ≤ scale n) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s : ℕ → Set (Fin h → G))
    (path : ∀ (_n : ℕ) (x : Fin h → G) (i : Fin h), Path (1 : G)
      ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1)))
    (hmetric : ∀ n x, x ∈ s n → ∀ i,
      PathMetricBound (path n x i) (A * scale n) (B * (1 + Real.log (2 + scale n))))
    (htemplate : ∀ n x, x ∈ s n → ∀ i t, ∃ z ∈ E i,
      ‖(π (path n x i t)).toAdd - scale n • z‖ ≤
        2 * scale n * η n + A * (1 + Real.log (2 + scale n)))
    (hend : ∀ n x, x ∈ s n → ∀ i : Fin h,
      ‖(π ((basedTuplePosition x i.val)⁻¹ * basedTuplePosition x (i.val + 1))).toAdd‖ ≤
        η n * scale n) :
    ∃ (RH R : ℕ → ℝ)
      (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier)),
      (∀ n, 0 ≤ RH n) ∧ (∀ n, 0 ≤ R n) ∧
      HasSubexponentialUpperBoundSeq scale RH ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n x, x ∈ s n →
        (∀ i, F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i) ∧
        (∀ i, ‖(finBasis ℝ H).equivFun
          (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n) ∧
        (∀ i, ‖eW (heightProjection T.character
          (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) :
            GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤ ((h : ℝ) * η n) * scale n) ∧
        (∀ i, (prefixCoordinateEquiv h).symm (p n x).1 i ∈
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) (E i) (β i) (scale n) (R n)) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
