-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_exists_bounded_box_profile_anchors
-- name    : OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:44:48.698474+00:00
-- url     : https://prove2.me/theorems/087b208f-2a55-4bb8-acaa-09ee830585d1
-- title:
--   OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanProfileAnchors.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanProfileAnchors.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Module`, `open scoped Manifold`):
--
--   ```lean
--   theorem exists_bounded_box_profile_anchors
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (s t : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) :
--       ∃ B lo : ℝ, 0 ≤ B ∧ 0 < lo ∧ ∀ (β γ : M.Bases),
--         IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--           (fun w => bracketWordExponent s w) β.val →
--         IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
--           (fun w => bracketWordExponent t w) γ.val →
--         ∀ r ε : ℝ, 1 ≤ r → ε ≤ lo → ∀ n k : F.N.carrier,
--         n ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
--           (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
--             (fun j => bracketWordExponent s (β.val j)) r) 1 →
--         k ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
--           (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
--             (fun j => bracketWordExponent t (γ.val j)) r) (Real.exp (r * ε)) →
--         dist 1 (F.inclusionN (n * k)) / r ≤ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.bracketWordExponent`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.evalBracketWord`, `OAI.PolycyclicRecognition.exponentialRescaleBasis`, `OAI.PolycyclicRecognition.wordListCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel` and `OAI.PolycyclicRecognition.WordBasisSelections.basis` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.exponentialCoordinateBox` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.IsMaximizingColumnBasis` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.IsGroupExponential` and `OAI.PolycyclicRecognition.TriangularAdjoint` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.CartanWordModel.cartan_independent_raw_chain_concentration`, `OAI.PolycyclicRecognition.CartanWordModel.exists_compact_measurable_box_profiles`, `OAI.PolycyclicRecognition.CartanWordModel.exists_published_sublinear_height`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_allowed_chain_concentration`, `OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_published_bounded_height`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_profile_estimates`, `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_published_suffix_concentration` and `OAI_PolycyclicRecognition_exists_compact_allowed_cartan_profiles` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanProfileAnchors.lean (declaration OAI.PolycyclicRecognition.exists_bounded_box_profile_anchors)

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

namespace PolycyclicRecognition

open Module
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
include T in
theorem exists_bounded_box_profile_anchors
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (s t : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) :
    ∃ B lo : ℝ, 0 ≤ B ∧ 0 < lo ∧ ∀ (β γ : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent t w) γ.val →
      ∀ r ε : ℝ, 1 ≤ r → ε ≤ lo → ∀ n k : F.N.carrier,
      n ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent s (β.val j)) r) 1 →
      k ∈ exponentialCoordinateBox (F.ExpN ∘ F.N.equiv)
        (exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
          (fun j => bracketWordExponent t (γ.val j)) r) (Real.exp (r * ε)) →
      dist 1 (F.inclusionN (n * k)) / r ≤ B := by
  sorry

end PolycyclicRecognition

end

end OAI
end
