-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalCandidate_evolution_of_bounds
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:49.225894+00:00
-- url     : https://prove2.me/theorems/a67411cd-9546-43a0-b944-c5303b282519
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCandidateEvolution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCandidateEvolution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma globalCandidate_evolution_of_bounds {T L C : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
--       (hL : let := geometricMetricSpace J α hs ht
--         VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
--       (hC : let := geometricMetricSpace J α hs ht
--         VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
--       (hcancel : ∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E t x y +
--         globalCorrection J α ht A E T t x y +
--         VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E)
--           (globalCorrection J α ht A E T) t x y = 0)
--       (v : X → FrameSpace A) (hv : Continuous v) :
--       ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
--         0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
--         (∀ a : PreL2 A J α hs ht true,
--           ⟪f,smoothL2 A J α hs ht true a⟫ =
--             ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
--         (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
--           ⟪U t,smoothL2 A J α hs ht true a⟫ =
--             kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
--             kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
--         (∀ a : PreL2 A J α hs ht true,
--           ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T)) ∧
--         (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
--           HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
--             (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.HeatBound` and `OAI.TamingCompatibility.GeometricHilbert.VolterraKernel.convolution` (definitions bundle `OAIQ239Tc008` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeLaplacian` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.geometricMetricSpace` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.framePairing`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCorrection`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalError`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernelWeakAction` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCandidateEvolution.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021

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
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma globalCandidate_evolution_of_bounds {T L C : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (hcancel : ∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E t x y +
      globalCorrection J α ht A E T t x y +
      VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E)
        (globalCorrection J α ht A E T) t x y = 0)
    (v : X → FrameSpace A) (hv : Continuous v) :
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T)) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
        HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
          (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
