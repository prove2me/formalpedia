-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_exists_closed_lift_hodge_bound
-- name    : OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:38.759625+00:00
-- url     : https://prove2.me/theorems/38feeaf7-8f25-4f90-b68a-11689206369d
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeLiftUnitBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeLiftUnitBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart`, `open ComplexMatrix TemperedDistribution HilbertSobolev Bundle Set Filter`, `open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace Topology`):
--
--   ```lean
--   lemma exists_closed_lift_hodge_bound
--       (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
--       ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
--         (∀ f, IsClosed (B f).val) ∧
--         (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
--         ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
--           ∀ a : PreL2 A J α hs ht true,
--             ‖smoothUnitEvaluation J g (B (smoothAntiProjection A J α hs ht a))‖ ≤
--               C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.antiInvariantPart` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.smoothAntiProjection` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.smoothUnitEvaluation` (definitions bundle `OAIQ239Tc020` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothShift` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsClosed`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeLiftUnitBound.lean (declaration OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound)

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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricChart
open ComplexMatrix TemperedDistribution HilbertSobolev Bundle Set Filter
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include D hD in

lemma exists_closed_lift_hodge_bound
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
        ∀ a : PreL2 A J α hs ht true,
          ‖smoothUnitEvaluation J g (B (smoothAntiProjection A J α hs ht a))‖ ≤
            C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  sorry
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end
