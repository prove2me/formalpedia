-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodge_regularized_positive_current_cross
-- name    : OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:26:07.440748+00:00
-- url     : https://prove2.me/theorems/13a8a1a1-bf8e-4910-9645-91a6537f9885
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeMixing.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeMixing.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart`, `open Set _root_.MeasureTheory`, `open scoped Manifold ContDiff RealInnerProductSpace`):
--
--   ```lean
--   lemma hodge_regularized_positive_current_cross :
--       ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
--         ∀ (C : HodgeSmoothingCover A J α hs ht D hD r hr)
--           (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
--           (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
--           (V : L2 A J α hs ht true),
--           (∀ a : PreL2 A J α hs ht true,
--             ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
--               (a-preAntiProjection A J α hs ht a))⟫ = 0) →
--           |⟪C.regularize g μ,V⟫| ≤ B*r*‖C.regularize g μ‖*‖V‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.unitMeasurable` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothShift`, `OAI.TamingCompatibility.GeometricHilbert.preAntiProjection` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.regularize` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeMixing.lean (declaration OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc022

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

lemma hodge_regularized_positive_current_cross :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
        (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
        (V : L2 A J α hs ht true),
        (∀ a : PreL2 A J α hs ht true,
          ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        |⟪C.regularize g μ,V⟫| ≤ B*r*‖C.regularize g μ‖*‖V‖ := by
  sorry
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
