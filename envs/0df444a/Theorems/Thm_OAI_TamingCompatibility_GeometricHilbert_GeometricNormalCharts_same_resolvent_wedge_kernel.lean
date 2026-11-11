-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_wedge_kernel
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:27:33.2142+00:00
-- url     : https://prove2.me/theorems/28bc5fb7-1aa2-4f77-b344-cd99f070d4d8
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel` of [lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeWedgeResolvent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeWedgeResolvent.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma same_resolvent_wedge_kernel (n : ℕ) :
--       let := geometricMetricSpace J α hs ht
--       ∃ T L Q : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
--         VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
--         VolterraKernel.HeatBound (geometricVolume A J α) n T Q (globalCorrection J α ht A E T) ∧
--         (∀ r : ℝ, 0 < r →
--           Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
--           Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
--         (∀ r : ℝ, 0 < r → ∀ x y : X,
--           VolterraBounds.weight n (r^2) x y *
--             ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
--               ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
--           VolterraBounds.weight n (r^2) x y *
--             ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
--               ((1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
--         ∀ (r : ℝ) (hr : 0 < r) (C : HodgeSmoothingCover A J α hs ht D hD r hr)
--           (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
--           2*ρ^2 ≤ T → ∀ g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type),
--           ∀ u v : MetricUnit g,
--           C.wedgeKernel g u v =
--             framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
--               ((HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r u.val.proj v.val.proj +
--                 HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r u.val.proj v.val.proj)
--                   (frameEncode J α ht A E v.val.proj ((preStar A J α hs ht (unitDual A J α hs ht E hE g v)).val v.val.proj))) +
--             B.gammaWedgeTailKernel g T hT.le r u v
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.MetricForms.Form` (definitions bundle `OAIQ239Tc000` of this split); `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.MetricUnit`, `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.gammaKernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.moment` and `OAI.TamingCompatibility.GeometricHilbert.VolterraBounds.weight` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.HeatBound` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.preStar` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameEncode`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.framePairing`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalError`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.unitDual` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover` and `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.wedgeKernel` (definitions bundle `OAIQ239Tc022` of this split); `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.gammaWedgeTailKernel` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeWedgeResolvent.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel)

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
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_wedge_kernel (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L Q : ℝ, ∃ hT : 0 < T, T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T Q (globalCorrection J α ht A E T) ∧
      (∀ r : ℝ, 0 < r →
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) ∧
        Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r p.1 p.2)) ∧
      (∀ r : ℝ, 0 < r → ∀ x y : X,
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
            ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4 ∧
        VolterraBounds.weight n (r^2) x y *
          ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
            ((1/120:ℝ)*(4*L*Q)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) ∧
      ∀ (r : ℝ) (hr : 0 < r) (C : HodgeSmoothingCover A J α hs ht D hD r hr)
        (ρ : ℝ) (hρ : 0 < ρ) (B : HodgeSmoothingCover A J α hs ht D hD ρ hρ),
        2*ρ^2 ≤ T → ∀ g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type),
        ∀ u v : MetricUnit g,
        C.wedgeKernel g u v =
          framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
            ((HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r u.val.proj v.val.proj +
              HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r u.val.proj v.val.proj)
                (frameEncode J α ht A E v.val.proj ((preStar A J α hs ht (unitDual A J α hs ht E hE g v)).val v.val.proj))) +
          B.gammaWedgeTailKernel g T hT.le r u v := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
