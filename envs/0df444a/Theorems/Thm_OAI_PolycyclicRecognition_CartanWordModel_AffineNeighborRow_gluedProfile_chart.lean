-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_AffineNeighborRow_gluedProfile_chart
-- name    : OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:34:18.914929+00:00
-- url     : https://prove2.me/theorems/14f30d71-5016-497a-88e8-2078e3e3b922
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNeighborRowChart.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNeighborRowChart.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule MeasureTheory Filter Set`, `open scoped Manifold Topology ENNReal NNReal`):
--
--   ```lean
--   theorem AffineNeighborRow.gluedProfile_chart
--       (hs : ∀ n, 1 ≤ D.scale n) :
--       (∀ n, Measurable (profile n)) ∧
--       (∀ n q, q ∈ (fun v => v * D.base n) ''
--           M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 ∪
--         (fun v => v * D.base n * D.step n) ''
--           M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 → ∀ z,
--         (profile n q).val z = rescaledMapProfile
--           (fun g => (π ((D.pair n).val.1 g)).toAdd) (D.center n) (F.inclusionN q)
--           (max (Real.log (D.scale n)) 0)
--           (F.profileChart (exponentialRescaleBasis
--             (WordBasisSelections.basis X (boundedBracketWords d) βD)
--             (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
--             (max (Real.log (D.scale n)) 0))) z) ∧
--       Tendsto (fun n => ProbabilityMeasure.map
--         (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
--           cell βcell (D.scale n) (D.base n))
--         (f := (fun q => (profile n q, profile n (q * D.step n)))) ((((D.gluedProfile_properties T M F hunimod eW π b₀ cell βcell X βD haarN chartN hchartN pivot shrink B δ S).1 n).prodMk (((D.gluedProfile_properties T M F hunimod eW π b₀ cell βcell X βD haarN chartN hchartN pivot shrink B δ S).1 n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 D.law)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.rescaledMapProfile`, `OAI.PolycyclicRecognition.CartanFactorModel.profileChart`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.basis` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput`, `OAI.PolycyclicRecognition.NormalizedPair`, `OAI.PolycyclicRecognition.glueNeighborProfile` and `OAI.PolycyclicRecognition.measurable_glueNeighborProfile` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow`, `OAI.PolycyclicRecognition.CartanWordModel.groupBox`, `OAI.PolycyclicRecognition.CartanWordModel.translatedGroupBoxProbability`, `OAI.PolycyclicRecognition.CartanWordModel.translated_groupBox_cell_properties`, `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile` and `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_properties` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.polar_offset_nonpos` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNeighborRowChart.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.AffineNeighborRow.gluedProfile_chart)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]

variable [Fintype I] [DecidableEq I]

variable (π : G →* Multiplicative W)
  (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (βcell : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (shrink B δ : ℝ)
  (S : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
  {Λ : ℝ≥0}
  (D : AffineNeighborRow T M F hunimod eW π b₀ cell βcell X βD
    haarN chartN hchartN pivot shrink B δ S (Λ := Λ))

local notation "profile" => D.gluedProfile T M F hunimod eW π b₀ cell βcell X βD
  haarN chartN hchartN pivot shrink B δ S

set_option maxHeartbeats 1000000 in
theorem AffineNeighborRow.gluedProfile_chart
    (hs : ∀ n, 1 ≤ D.scale n) :
    (∀ n, Measurable (profile n)) ∧
    (∀ n q, q ∈ (fun v => v * D.base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 ∪
      (fun v => v * D.base n * D.step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell βcell (D.scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((D.pair n).val.1 g)).toAdd) (D.center n) (F.inclusionN q)
        (max (Real.log (D.scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (D.scale n)) 0))) z) ∧
    Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        cell βcell (D.scale n) (D.base n))
      (f := (fun q => (profile n q, profile n (q * D.step n)))) ((((D.gluedProfile_properties T M F hunimod eW π b₀ cell βcell X βD haarN chartN hchartN pivot shrink B δ S).1 n).prodMk (((D.gluedProfile_properties T M F hunimod eW π b₀ cell βcell X βD haarN chartN hchartN pivot shrink B δ S).1 n).comp (continuous_id.mul continuous_const).measurable)).aemeasurable)) atTop (𝓝 D.law) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
