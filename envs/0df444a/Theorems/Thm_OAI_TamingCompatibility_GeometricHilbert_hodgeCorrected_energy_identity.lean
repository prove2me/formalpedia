-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodgeCorrected_energy_identity
-- name    : OAI.TamingCompatibility.GeometricHilbert.hodgeCorrected_energy_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:15:18.423555+00:00
-- url     : https://prove2.me/theorems/2c42f4db-bb6a-4ab8-8456-dd7bad05031e
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.hodgeCorrected_energy_identity: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrected_energy_identity` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCorrectionRegularization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCorrectionRegularization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart`, `open Set _root_.MeasureTheory`, `open scoped Manifold ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma hodgeCorrected_energy_identity
--       (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
--       (hBc : ∀ f, IsClosed (B f).val)
--       (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
--       (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
--       (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
--       (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
--         unitMeasureCurrent J g μ β = 0) (r : ℝ) (hr : 0 < r)
--       (C : HodgeSmoothingCover A J α hs ht D hD r hr)
--       (hrep : hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
--         (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr)) :
--       ⟪C.regularize g μ,l2Star A J α hs ht (C.regularize g μ)⟫ +
--         2*⟪C.regularize g μ,hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr⟫+
--         ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖^2 = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.antiInvariantPart`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.l2Star`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module` and `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.unitMeasureCurrent` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.regularize` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrectionSource` (definitions bundle `OAIQ239Tc024` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeCubeRepresents` (definitions bundle `OAIQ239Tc027` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrectionRegularize` (definitions bundle `OAIQ239Tc033` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsInvariant`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCorrectionRegularization.lean (declaration OAI.TamingCompatibility.GeometricHilbert.hodgeCorrected_energy_identity)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc033

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

lemma hodgeCorrected_energy_identity
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (hBc : ∀ f, IsClosed (B f).val)
    (hBR : ∀ f, antiInvariantPart J (B f).val = f.val.val)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J g μ β = 0) (r : ℝ) (hr : 0 < r)
    (C : HodgeSmoothingCover A J α hs ht D hD r hr)
    (hrep : hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
      (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr)) :
    ⟪C.regularize g μ,l2Star A J α hs ht (C.regularize g μ)⟫ +
      2*⟪C.regularize g μ,hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr⟫+
      ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖^2 = 0 := by
  sorry
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
