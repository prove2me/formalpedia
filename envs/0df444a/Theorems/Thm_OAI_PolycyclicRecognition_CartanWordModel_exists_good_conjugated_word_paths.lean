-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_good_conjugated_word_paths
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:36:00.178956+00:00
-- url     : https://prove2.me/theorems/02ce0911-c7e7-4187-b888-60c230024e3c
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanGoodWordPaths.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanGoodWordPaths.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Filter`, `open scoped Manifold Topology NNReal`):
--
--   ```lean
--   theorem exists_good_conjugated_word_paths
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (π : G →* Multiplicative W)
--       (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
--       (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
--       (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
--       (βD : WordBasisSelections X (boundedBracketWords d))
--       (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
--         (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
--       (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
--       (pivot : H) (v : Fin M.letterCount → H)
--       (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
--       (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
--       (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
--       (s : Fin M.letterCount → ℝ)
--       (hs : ∀ i, cartanHeightWeight T H (M.weight i)
--         (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
--       {B : ℝ} (hB : 0 ≤ B) :
--       let b := WordBasisSelections.basis X (boundedBracketWords d) βD
--       let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
--       let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
--       let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
--         ((heightProjection T.character).comp H.incl.toLinearMap)
--       ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
--         IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
--         (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
--         ∀ᶠ n in atTop, ∀ (m : ℕ) (mode : Fin m → Fin M.letterCount) (coeff : Fin m → ℝ),
--           (∀ j, |coeff j| ≤ B * Real.exp (scale n * s (mode j))) →
--           ∀ (Good : Set F.N.carrier) (x : G) (k n₀ : F.N.carrier),
--           let u := fun j => F.ExpN (F.N.equiv (coeff j • M.letter (mode j)))
--           let word := fun j => k * u j * k⁻¹
--           WordSheetsGood Good n₀ (List.ofFn word) →
--           ∀ (J : G → W) (K : ℝ≥0), LipschitzWith K J →
--           ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
--           (∀ q ∈ Good, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
--             ‖rescaledMapProfile J x (F.inclusionN (q * k)) (Real.log (scale n))
--                 (fun z => Exp ((br n).equivFun.symm z)) z -
--               (A (height (b.equivFun.symm z)) + offset)‖ ≤ ε) →
--           ∃ path : Path
--               (x * F.inclusionN (n₀ * k) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
--               (x * F.inclusionN (n₀ * (List.ofFn word).prod * k) *
--                 Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
--             PathMetricBound path ((C * scale n) * 2 ^ m)
--               ((C * (1 + Real.log (2 + scale n))) * 2 ^ m) ∧
--             ∀ t, ∃ w ∈ E,
--               ‖J (path t) - J (x * F.inclusionN (n₀ * k) *
--                   Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
--                 scale n • A (w - height pivot)‖ ≤
--                   2 * scale n * ε + K * (C * Real.log (2 + scale n))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.WordBasisSelections`, `OAI.PolycyclicRecognition.boundedBracketWords`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanHeightWeight`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.rescaledMapProfile`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.basis` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.PathMetricBound` and `OAI.PolycyclicRecognition.WordSheetsGood` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.good_affine_templates_support_le` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanGoodWordPaths.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_good_conjugated_word_paths)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter
open scoped Manifold Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

set_option maxHeartbeats 1000000 in
theorem exists_good_conjugated_word_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (pivot : H) (v : Fin M.letterCount → H)
    (E V : Set W) (hE : Convex ℝ E) (hpivot : eW (heightProjection T.character pivot) ∈ E)
    (hV : IsOpen V) (hVconv : Convex ℝ V) (hEV : E ⊆ V)
    (hv : ∀ i, eW (heightProjection T.character (pivot + v i : H)) ∈ E)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, cartanHeightWeight T H (M.weight i)
      (eW.symm (eW (heightProjection T.character (pivot + v i : H)))) = s i)
    {B : ℝ} (hB : 0 ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    let br := fun n => exponentialRescaleBasis b cost (Real.log (scale n))
    let height : H →ₗ[ℝ] W := eW.toLinearMap.comp
      ((heightProjection T.character).comp H.incl.toLinearMap)
    ∃ (Q : Set (Fin (finrank ℝ H) → ℝ)) (C : ℝ),
      IsCompact Q ∧ Q ⊆ {z | height (b.equivFun.symm z) ∈ V} ∧ 0 ≤ C ∧
      (∀ᶠ n in atTop, (br n).equivFun (scale n • pivot) ∈ Q) ∧
      ∀ᶠ n in atTop, ∀ (m : ℕ) (mode : Fin m → Fin M.letterCount) (coeff : Fin m → ℝ),
        (∀ j, |coeff j| ≤ B * Real.exp (scale n * s (mode j))) →
        ∀ (Good : Set F.N.carrier) (x : G) (k n₀ : F.N.carrier),
        let u := fun j => F.ExpN (F.N.equiv (coeff j • M.letter (mode j)))
        let word := fun j => k * u j * k⁻¹
        WordSheetsGood Good n₀ (List.ofFn word) →
        ∀ (J : G → W) (K : ℝ≥0), LipschitzWith K J →
        ∀ (A : W →ₗ[ℝ] W) (offset : W) (ε : ℝ),
        (∀ q ∈ Good, ∀ z ∈ Q, height (b.equivFun.symm z) ∈ E →
          ‖rescaledMapProfile J x (F.inclusionN (q * k)) (Real.log (scale n))
              (fun z => Exp ((br n).equivFun.symm z)) z -
            (A (height (b.equivFun.symm z)) + offset)‖ ≤ ε) →
        ∃ path : Path
            (x * F.inclusionN (n₀ * k) * Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
            (x * F.inclusionN (n₀ * (List.ofFn word).prod * k) *
              Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))),
          PathMetricBound path ((C * scale n) * 2 ^ m)
            ((C * (1 + Real.log (2 + scale n))) * 2 ^ m) ∧
          ∀ t, ∃ w ∈ E,
            ‖J (path t) - J (x * F.inclusionN (n₀ * k) *
                Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) -
              scale n • A (w - height pivot)‖ ≤
                2 * scale n * ε + K * (C * Real.log (2 + scale n)) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
