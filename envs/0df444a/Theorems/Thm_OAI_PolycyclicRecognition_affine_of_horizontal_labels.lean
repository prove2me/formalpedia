-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_affine_of_horizontal_labels
-- name    : OAI.PolycyclicRecognition.affine_of_horizontal_labels
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:11:04.262802+00:00
-- url     : https://prove2.me/theorems/6568ec44-4c51-4e38-8e66-aaaa7cd582d8
-- title:
--   OAI.PolycyclicRecognition.affine_of_horizontal_labels: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.affine_of_horizontal_labels` of [lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/AffineFromHorizontalLabels.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/AffineFromHorizontalLabels.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Set Filter MeasureTheory Module`, `open scoped NNReal`):
--
--   ```lean
--   theorem affine_of_horizontal_labels
--       {H V W I B K J L : Type*}
--       [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
--       [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
--       [MeasurableSpace V] [BorelSpace V]
--       [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
--       [Fintype I] [Fintype B] [Nonempty B]
--       [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
--       {c : ℕ} (a : DynkinCoefficients c 2) (br : V →L[ℝ] V →L[ℝ] V)
--       (hbr : IsLieBracket br) (hg : PolynomialGroupLaws (dynkinProduct a br))
--       (hc : ExponentialConjugationLaw (dynkinProduct a br) br)
--       (D : H →L[ℝ] V) (X : K → H) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma K)
--       (hw₀ : ∀ j, evalBilinearWord br (fun k => D (X k)) (w₀ j) = b₀ j)
--       (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a br) hg))
--       [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
--       (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a br) hg))
--       (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
--       (f : PolynomialCoordinateGroup (dynkinProduct a br) hg → W) (hf : Continuous f)
--       (π : PolynomialCoordinateGroup (dynkinProduct a br) hg →* Multiplicative W)
--       (p : V →L[ℝ] W) (hp : Function.Surjective (p.comp D))
--       (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
--       (P : SupportDatum W I B) (hweights : ∀ i, P.weight i ≠ 0)
--       (σ : I → Bool) (hσ : (weightChamber (fun i => (P.weight i).toContinuousLinearMap) σ).Nonempty)
--       (label : PolynomialCoordinateGroup (dynkinProduct a br) hg → L)
--       (hlabel : Measurable label) (A : L → templateSymmetryGroup P)
--       (hbase : ∀ v : H, ∀ᵐ g ∂μ, g ∈ Ω →
--         HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
--           ((A (label g)).val (p (D v))) 0)
--       (C : H → ℝ≥0)
--       (hlip : ∀ v g, LipschitzOnWith (C v)
--         (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
--         {t | g * PolynomialCoordinateGroup.exp _ hg (t • D v) ∈ Ω})
--       (hvol : ∀ v (T : ℝ), 0 < T →
--         ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T,
--           T * P.segmentSupport (p (D v)) ≤ P.templateSupport
--             ((fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v))) '' Icc 0 T)) :
--       ∃ l b, ∀ g ∈ Ω, f g = (A l).val ((π g).toAdd) + b
--   ```
--
--   **Definitions.** The statement is written with `OAI.PolycyclicRecognition.SupportDatum` and `OAI.PolycyclicRecognition.SupportDatum.segmentSupport` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.DynkinCoefficients`, `OAI.PolycyclicRecognition.dynkinProduct` and `OAI.PolycyclicRecognition.evalBilinearWord` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ExponentialConjugationLaw`, `OAI.PolycyclicRecognition.IsLieBracket`, `OAI.PolycyclicRecognition.PolynomialCoordinateGroup`, `OAI.PolycyclicRecognition.PolynomialGroupLaws`, `OAI.PolycyclicRecognition.PolynomialCoordinateGroup.exp`, `OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instGroup`, `OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instMeasurableSpace` and `OAI.PolycyclicRecognition.PolynomialCoordinateGroup.instTopologicalSpace` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.flowLineBase` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.templateSymmetryGroup` and `OAI.PolycyclicRecognition.SupportDatum.templateSupport` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.weightChamber` (definitions bundle `OAIQ093D010` of this split).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.cartan_supported_profile_affine_sequence` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Analysis/AffineFromHorizontalLabels.lean (declaration OAI.PolycyclicRecognition.affine_of_horizontal_labels)

import Mathlib
import Definitions.Def_OAIQ093D007
import Definitions.Def_OAIQ093D010

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.finitelyGeneratedSubgroupIndex_countable _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal

theorem affine_of_horizontal_labels
    {H V W I B K J L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {c : ℕ} (a : DynkinCoefficients c 2) (br : V →L[ℝ] V →L[ℝ] V)
    (hbr : IsLieBracket br) (hg : PolynomialGroupLaws (dynkinProduct a br))
    (hc : ExponentialConjugationLaw (dynkinProduct a br) br)
    (D : H →L[ℝ] V) (X : K → H) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma K)
    (hw₀ : ∀ j, evalBilinearWord br (fun k => D (X k)) (w₀ j) = b₀ j)
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a br) hg → W) (hf : Continuous f)
    (π : PolynomialCoordinateGroup (dynkinProduct a br) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective (p.comp D))
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (P : SupportDatum W I B) (hweights : ∀ i, P.weight i ≠ 0)
    (σ : I → Bool) (hσ : (weightChamber (fun i => (P.weight i).toContinuousLinearMap) σ).Nonempty)
    (label : PolynomialCoordinateGroup (dynkinProduct a br) hg → L)
    (hlabel : Measurable label) (A : L → templateSymmetryGroup P)
    (hbase : ∀ v : H, ∀ᵐ g ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
        ((A (label g)).val (p (D v))) 0)
    (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v)
      (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v)))
      {t | g * PolynomialCoordinateGroup.exp _ hg (t • D v) ∈ Ω})
    (hvol : ∀ v (T : ℝ), 0 < T →
      ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T,
        T * P.segmentSupport (p (D v)) ≤ P.templateSupport
          ((fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • D v))) '' Icc 0 T)) :
    ∃ l b, ∀ g ∈ Ω, f g = (A l).val ((π g).toAdd) + b := by
  sorry

end PolycyclicRecognition

end

end OAI
end
