-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_supported_profile_increment_of_flow
-- name    : OAI.PolycyclicRecognition.supported_profile_increment_of_flow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:13:56.947731+00:00
-- url     : https://prove2.me/theorems/74ecca9b-8fab-471d-bf18-9b27f7af8199
-- title:
--   OAI.PolycyclicRecognition.supported_profile_increment_of_flow: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.supported_profile_increment_of_flow` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/FlowSupportedProfileIncrement.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/FlowSupportedProfileIncrement.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Filter MeasureTheory Set Metric`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem supported_profile_increment_of_flow
--       {V W A G ι : Type*} [MetricSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
--       [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
--       [MeasurableSpace A] [Group G] [MetricSpace G] [ProperSpace G]
--       [IsTopologicalGroup G] [IsIsometricSMul G G]
--       {Λ Kπ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
--       (S : Set C(V, W)) (hS : IsCompact S) [MeasurableSpace S] [BorelSpace S]
--       (π : G →* Multiplicative W) (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
--       {l : Filter ι} [l.NeBot]
--       (samples : ι → ProbabilityMeasure A) (profile : ι → A → S)
--       (hprofile : ∀ i, Measurable (profile i)) (ν : ProbabilityMeasure S)
--       (hν : Tendsto (fun i => ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) l (𝓝 ν))
--       (m : Measure V) [m.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts m]
--       (Fs : ι → C(V × ℝ, V)) (F : C(V × ℝ, V)) (hF : Tendsto Fs l (𝓝 F))
--       (hpres : ∀ i t, MeasurePreserving (fun z => Fs i (z, t)) m m)
--       (chart : ι → A × V → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
--       (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
--       (hmul : ∀ s t, d (s + t) = d s * d t)
--       (r : ι → ℝ) (hr : Tendsto r l atTop) {T : ℝ} (hT : 0 < T)
--       (hmove : ∀ i a z t, (d (r i * t))⁻¹ • chart i (a, z) = chart i (a, Fs i (z, t)))
--       (hidentity : ∀ i, ∀ᵐ a ∂(samples i : Measure A), ∀ z,
--         (r i * T)⁻¹ • pairHeight π (d (r i * T)) (chart i (a, z)) =
--         T⁻¹ • ((profile i a).val (Fs i (z, T)) - (profile i a).val z))
--       {U : Set V} (hU : IsOpen U) (z : V) (hseg : ∀ t ∈ Icc 0 T, F (z, t) ∈ U)
--       (hinvariant : ∀ (ρ : C(V, ℝ)) (hi : Integrable ρ m) (hp : ∀ x, 0 ≤ ρ x)
--         (hm : ∫ x, ρ x ∂m = 1), HasCompactSupport ρ → tsupport ρ ⊆ U →
--         ∀ (u : Ultrafilter ι), (u : Filter ι) ≤ l →
--         ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
--         Tendsto (fun i => productOccupationLaw (samples i)
--           (densityProbabilityMeasure m ρ hi hp hm) (chart i)) u (𝓝 μ) →
--         SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _))
--       {B : Set W} (hB : IsCompact B) {b : W} (hb : b ∈ B)
--       (hconvex : IsClosed (convexHull ℝ B))
--       (hstationary : ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
--         SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _) →
--         Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
--           infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) B ∂(μ : Measure _)) atTop (𝓝 0))
--       {f : S} (hf : f ∈ (ν : Measure S).support) :
--       T⁻¹ • (f.val (F (z, T)) - f.val z) ∈ convexHull ℝ B
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.NormalizedPair` and `OAI.PolycyclicRecognition.normalizedPairAction` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.densityProbabilityMeasure` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.pairHeight` (definitions bundle `OAIQ093D010` of this split); `OAI.PolycyclicRecognition.productOccupationLaw` (definitions bundle `OAIQ093D011` of this split).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.cartan_profile_increment_mem_template_sequence` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/FlowSupportedProfileIncrement.lean (declaration OAI.PolycyclicRecognition.supported_profile_increment_of_flow)

import Mathlib
import Definitions.Def_OAIQ093D010
import Definitions.Def_OAIQ093D011

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory Set Metric
open scoped Topology NNReal

theorem supported_profile_increment_of_flow
    {V W A G ι : Type*} [MetricSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace A] [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    {Λ Kπ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (S : Set C(V, W)) (hS : IsCompact S) [MeasurableSpace S] [BorelSpace S]
    (π : G →* Multiplicative W) (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    {l : Filter ι} [l.NeBot]
    (samples : ι → ProbabilityMeasure A) (profile : ι → A → S)
    (hprofile : ∀ i, Measurable (profile i)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun i => ProbabilityMeasure.map (samples i) (f := (profile i)) (by first | exact (hprofile i).aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)) l (𝓝 ν))
    (m : Measure V) [m.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts m]
    (Fs : ι → C(V × ℝ, V)) (F : C(V × ℝ, V)) (hF : Tendsto Fs l (𝓝 F))
    (hpres : ∀ i t, MeasurePreserving (fun z => Fs i (z, t)) m m)
    (chart : ι → A × V → NormalizedPair G Λ) (hchart : ∀ i, Measurable (chart i))
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (r : ι → ℝ) (hr : Tendsto r l atTop) {T : ℝ} (hT : 0 < T)
    (hmove : ∀ i a z t, (d (r i * t))⁻¹ • chart i (a, z) = chart i (a, Fs i (z, t)))
    (hidentity : ∀ i, ∀ᵐ a ∂(samples i : Measure A), ∀ z,
      (r i * T)⁻¹ • pairHeight π (d (r i * T)) (chart i (a, z)) =
      T⁻¹ • ((profile i a).val (Fs i (z, T)) - (profile i a).val z))
    {U : Set V} (hU : IsOpen U) (z : V) (hseg : ∀ t ∈ Icc 0 T, F (z, t) ∈ U)
    (hinvariant : ∀ (ρ : C(V, ℝ)) (hi : Integrable ρ m) (hp : ∀ x, 0 ≤ ρ x)
      (hm : ∫ x, ρ x ∂m = 1), HasCompactSupport ρ → tsupport ρ ⊆ U →
      ∀ (u : Ultrafilter ι), (u : Filter ι) ≤ l →
      ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
      Tendsto (fun i => productOccupationLaw (samples i)
        (densityProbabilityMeasure m ρ hi hp hm) (chart i)) u (𝓝 μ) →
      SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _))
    {B : Set W} (hB : IsCompact B) {b : W} (hb : b ∈ B)
    (hconvex : IsClosed (convexHull ℝ B))
    (hstationary : ∀ μ : ProbabilityMeasure (NormalizedPair G Λ),
      SMulInvariantMeasure G (NormalizedPair G Λ) (μ : Measure _) →
      Tendsto (fun L : ℕ => ∫ p : NormalizedPair G Λ,
        infDist ((L : ℝ)⁻¹ • pairHeight π (d L) p) B ∂(μ : Measure _)) atTop (𝓝 0))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    T⁻¹ • (f.val (F (z, T)) - f.val z) ∈ convexHull ℝ B := by
  sorry

end PolycyclicRecognition

end

end OAI
end
