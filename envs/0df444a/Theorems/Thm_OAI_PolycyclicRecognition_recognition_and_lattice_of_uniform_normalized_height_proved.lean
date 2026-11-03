-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_recognition_and_lattice_of_uniform_normalized_height_proved
-- name    : OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:45:32.444207+00:00
-- url     : https://prove2.me/theorems/87c36370-c218-4e81-8bc4-694ef098d50d
-- title:
--   OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved` of [lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/RecognitionWithoutKMN.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/RecognitionWithoutKMN.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Set`, `open scoped Manifold NNReal`):
--
--   ```lean
--   theorem recognition_and_lattice_of_uniform_normalized_height_proved
--       (dekimpe : DekimpeLatticeRealizationInput)
--       {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
--       [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
--       [DiscreteTopology J] [ProperSpace J]
--       [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
--       (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
--       (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
--       {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
--       [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
--       [SimplyConnectedSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
--       {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
--       (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
--       (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
--       (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
--       (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
--       (u : MetricQuasiEquivalence J G)
--       (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
--       {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
--       (D : SupportDatum W I B₀)
--       {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
--       (c : ControlledContraction G)
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ s) ≤ dist 1 g * |t - s|)
--       (hheight : ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
--         ∃ label : NormalizedPair G Λ → templateSymmetryGroup D,
--           ∃ B : ℝ, 0 ≤ B ∧
--             ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B) :
--       IsVirtuallyPolycyclic J ∧
--         ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
--           ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
--             IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.SupportDatum` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NormalizedPair` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ControlledContraction`, `OAI.PolycyclicRecognition.DekimpeLatticeRealizationInput`, `OAI.PolycyclicRecognition.GromovPolynomialGrowthInput` and `OAI.PolycyclicRecognition.MetricQuasiEquivalence` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.templateSymmetryGroup` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.IsUniformLattice`, `OAI.PolycyclicRecognition.IsVirtuallyPolycyclic`, `OAI.PolycyclicRecognition.SimplyConnectedSolvableLieModel`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.group_recognition_of_gromov` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Algebra/RecognitionWithoutKMN.lean (declaration OAI.PolycyclicRecognition.recognition_and_lattice_of_uniform_normalized_height_proved)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D007

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold NNReal

theorem recognition_and_lattice_of_uniform_normalized_height_proved
    (dekimpe : DekimpeLatticeRealizationInput)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (hPfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (u : MetricQuasiEquivalence J G)
    (gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K)
    {I B₀ : Type*} [Fintype I] [Fintype B₀] [Nonempty B₀]
    (D : SupportDatum W I B₀)
    {L : ℝ≥0} (hπ : LipschitzWith L (fun g => (π g).toAdd))
    (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|)
    (hheight : ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ label : NormalizedPair G Λ → templateSymmetryGroup D,
        ∃ B : ℝ, 0 ≤ B ∧
          ∀ p x, ‖(π (p.val.1 x)).toAdd - (label p).val (π x).toAdd‖ ≤ B) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  sorry

end PolycyclicRecognition

end

end OAI
end
