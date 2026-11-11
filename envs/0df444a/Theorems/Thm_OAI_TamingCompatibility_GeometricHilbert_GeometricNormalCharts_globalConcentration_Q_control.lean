-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalConcentration_Q_control
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:58.179109+00:00
-- url     : https://prove2.me/theorems/d32bc85e-03dd-4d31-8fd6-a265434c2f7d
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control` of [lean/OAI/Geometry/TamingCompatibility/Concentration/ConcentrationGlobalError.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/ConcentrationGlobalError.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter _root_.MeasureTheory Hermitian Concentration`, `open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal`):
--
--   ```lean
--   lemma globalConcentration_Q_control
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
--       (Q : L2 A J α hs ht true) :
--       ∃ e : ℝ → X → ℝ,
--         (∀ r, 0 < r → ∀ x, 0 ≤ e r x) ∧
--         (∀ r, 0 < r → Integrable (e r) (geometricVolume A J α)) ∧
--         Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
--         ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x,
--           ‖l2Coefficients A J α hs ht E hE Q x‖ *
--             ‖normalizedFrameEncode A J α ht E x
--               (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val x)‖ ≤ C*e r x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricForms.Form` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable`, `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.scalarDifferential` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.ManifoldForms.wedgeOne` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module` and `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.HilbertFrame`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.l2Coefficients`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalizedFrameEncode` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.taming_implies_compatibility` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/ConcentrationGlobalError.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_Q_control)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc020
import Definitions.Def_OAIQ239Tc021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory Hermitian Concentration
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel

include hE in
lemma globalConcentration_Q_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) :
    ∃ e : ℝ → X → ℝ,
      (∀ r, 0 < r → ∀ x, 0 ≤ e r x) ∧
      (∀ r, 0 < r → Integrable (e r) (geometricVolume A J α)) ∧
      Tendsto (fun r => ∫ x, e r x ∂geometricVolume A J α) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x,
        ‖l2Coefficients A J α hs ht E hE Q x‖ *
          ‖normalizedFrameEncode A J α ht E x
            (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val x)‖ ≤ C*e r x := by
  sorry
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end
