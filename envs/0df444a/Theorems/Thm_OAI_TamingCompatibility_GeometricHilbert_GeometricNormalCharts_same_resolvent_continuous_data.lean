-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_continuous_data
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:35.01423+00:00
-- url     : https://prove2.me/theorems/4b95ee2b-8519-4838-a474-db8282020d07
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data` of [lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeContinuousResolvent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeContinuousResolvent.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma same_resolvent_continuous_data (n : ℕ) :
--       let := geometricMetricSpace J α hs ht
--       ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
--         VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
--         VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
--         (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
--         ∀ v : X → FrameSpace A, Continuous v →
--         ∃ f : L2 A J α hs ht true,
--           (∀ a : PreL2 A J α hs ht true,
--             ⟪f,smoothL2 A J α hs ht true a⟫ =
--               ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
--           (∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
--             ⟪(hodgeRegularization A J α hs ht r ^ 2) f,smoothL2 A J α hs ht true a⟫ =
--               (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
--                 (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val (r^2*s) +
--                  kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val (r^2*s))) +
--               ⟪hodgeGammaTailAction A J α hs ht D hD T r f,smoothL2 A J α hs ht true a⟫) ∧
--           (∀ N : ℕ, ∀ r : ℝ, 0 < r →
--             ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
--               ((1/120 : ℝ) * HodgeKernelBounds.moment 5 (1/2) * (N.factorial : ℝ) * (2/T)^N) *
--                 r^(2*N)*‖f‖)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaWeight` and `OAI.TamingCompatibility.GeometricHilbert.HodgeKernelBounds.moment` (definitions bundle `OAIQ239Tc004` of this split); `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.HeatBound` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.HodgeChart.Data` (definitions bundle `OAIQ239Tc015` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.framePairing`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalError`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernelWeakAction` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeRegularization` (definitions bundle `OAIQ239Tc027` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeGammaTailAction` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_smooth_spatial` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeContinuousResolvent.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc028

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
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
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
lemma same_resolvent_continuous_data (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
      ∀ v : X → FrameSpace A, Continuous v →
      ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        (∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) f,smoothL2 A J α hs ht true a⟫ =
            (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
              (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val (r^2*s) +
               kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val (r^2*s))) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r f,smoothL2 A J α hs ht true a⟫) ∧
        (∀ N : ℕ, ∀ r : ℝ, 0 < r →
          ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
            ((1/120 : ℝ) * HodgeKernelBounds.moment 5 (1/2) * (N.factorial : ℝ) * (2/T)^N) *
              r^(2*N)*‖f‖) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end

end

end OAI
end
