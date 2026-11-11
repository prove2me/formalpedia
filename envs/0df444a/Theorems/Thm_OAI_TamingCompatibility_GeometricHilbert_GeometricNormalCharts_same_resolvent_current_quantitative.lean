-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_current_quantitative
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:27.450307+00:00
-- url     : https://prove2.me/theorems/a666e7a6-21f8-41c9-b400-25ff68d8a16e
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeQuantitative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeQuantitative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma same_resolvent_current_quantitative (n : ℕ) :
--       let := geometricMetricSpace J α hs ht
--       ∃ T C : ℝ, ∃ hT : 0 < T, 0 ≤ C ∧ T ≤ 1 ∧
--         (∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
--           VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
--             |unitCurrentKernel A J α ht E g
--               (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| ≤ C/r^4 ∧
--           VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
--             |unitCurrentKernel A J α ht E g
--               (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤ C/r^2) ∧
--         ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
--           (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
--           2*ρ^2 ≤ T → ∀ u v : MetricUnit g,
--           S.innerKernel g u v =
--             unitCurrentKernel A J α ht E g
--               (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
--             unitCurrentKernel A J α ht E g
--               (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v +
--             B.gammaTailKernel g T hT.le r u v
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricUnit` and `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.gammaKernel` and `OAI.TamingCompatibility.GeometricHilbert.VolterraBounds.weight` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalError`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.unitCurrentKernel` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.innerKernel` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.gammaTailKernel` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeQuantitative.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_current_quantitative (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T C : ℝ, ∃ hT : 0 < T, 0 ≤ C ∧ T ≤ 1 ∧
      (∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| ≤ C/r^4 ∧
        VolterraBounds.weight n (r^2) u.val.proj v.val.proj *
          |unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| ≤ C/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ u v : MetricUnit g,
        S.innerKernel g u v =
          unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v +
          unitCurrentKernel A J α ht E g
            (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v +
          B.gammaTailKernel g T hT.le r u v := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
