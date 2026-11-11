-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_separating_current_L2_correction
-- name    : OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:08.331402+00:00
-- url     : https://prove2.me/theorems/93b98fc8-7453-4df6-9bca-aa5495a74c34
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAtlasCorrection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAtlasCorrection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts Filter`, `open Set _root_.MeasureTheory`, `open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal`):
--
--   ```lean
--   theorem separating_current_L2_correction
--       (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
--       (ht : Tames α J) (hc : IsClosed α)
--       (A : FiniteCharts X)
--       (E : ∀ p : A.centers, ParametrixData J α ht p.val)
--       (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
--       (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
--       (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
--       (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
--       ∃ Q : L2 A J α hs ht true,
--         l2AntiProjection A J α hs ht Q = Q ∧
--         l2Star A J α hs ht Q = Q ∧
--         (∀ a : smoothForms X 2, IsClosed a.val →
--           unitMeasureCurrent J (hermitianMetric J α hs ht) μ a+
--             ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) ∧
--         ⟪Q,smoothL2 A J α hs ht true ⟨α,hs⟩⟫ = -1
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.l2Star`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.hermitianMetric` and `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.taming_implies_compatibility` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeAtlasCorrection.lean (declaration OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction)

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
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts Filter
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel

theorem separating_current_L2_correction
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (hc : IsClosed α)
    (A : FiniteCharts X)
    (E : ∀ p : A.centers, ParametrixData J α ht p.val)
    (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
    (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
    (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ Q : L2 A J α hs ht true,
      l2AntiProjection A J α hs ht Q = Q ∧
      l2Star A J α hs ht Q = Q ∧
      (∀ a : smoothForms X 2, IsClosed a.val →
        unitMeasureCurrent J (hermitianMetric J α hs ht) μ a+
          ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) ∧
      ⟪Q,smoothL2 A J α hs ht true ⟨α,hs⟩⟫ = -1 := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end OAI
end
