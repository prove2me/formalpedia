-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalConcentration_current_control
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:21.260996+00:00
-- url     : https://prove2.me/theorems/6dc7c4e9-5c25-4c3b-b6cb-8be95e90146f
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control` of [lean/OAI/Geometry/TamingCompatibility/Concentration/ConcentrationGlobalError.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/ConcentrationGlobalError.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume`, `open Set Filter _root_.MeasureTheory Hermitian Concentration`, `open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal`):
--
--   ```lean
--   lemma globalConcentration_current_control
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
--       (Q : L2 A J α hs ht true)
--       (hT : ∀ a : smoothForms X 2, IsClosed a.val →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
--       ∃ e : ℝ → MetricUnit (hermitianMetric J α hs ht) → ℝ,
--         (∀ r, 0 < r → ∀ u, 0 ≤ e r u) ∧
--         (∀ r, 0 < r → Integrable (e r) μ) ∧
--         Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
--         ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u,
--           |eval (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val)
--             u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤
--           C*(globalConcentration A J α hs ht E μ r u.val.proj+e r u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.scalarDifferential` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.GeometricChart.Data`, `OAI.TamingCompatibility.ManifoldForms.smoothForms`, `OAI.TamingCompatibility.ManifoldForms.wedgeOne` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` and `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames`, `OAI.TamingCompatibility.TwoForm` and `OAI.TamingCompatibility.eval` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.taming_implies_compatibility` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Concentration/ConcentrationGlobalError.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalConcentration_current_control)

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

include hE hD hG in
lemma globalConcentration_current_control
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    ∃ e : ℝ → MetricUnit (hermitianMetric J α hs ht) → ℝ,
      (∀ r, 0 < r → ∀ u, 0 ≤ e r u) ∧
      (∀ r, 0 < r → Integrable (e r) μ) ∧
      Tendsto (fun r => ∫ u, e r u ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (globalConcentration A J α hs ht E μ r)) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ≤
        C*(globalConcentration A J α hs ht E μ r u.val.proj+e r u) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end
