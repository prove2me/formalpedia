-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leading_time_primitive
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:54.74267+00:00
-- url     : https://prove2.me/theorems/d1a2f156-d90d-4957-8769-ededd31f06cd
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeInputInitial.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeInputInitial.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma leading_time_primitive (y : X) (v : FrameSpace A)
--       (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
--       (∫ s in (0:ℝ)..t,
--         kernelTestSlice A J α ht E (globalResidual J α ht A E) y v a.val s -
--         kernelTestSlice A J α ht E (globalLeading J α ht A E) y v
--           (hodgeLaplacian A J α hs ht a).val s) =
--       kernelTestSlice A J α ht E (globalLeading J α ht A E) y v a.val t -
--         framePairing A J α ht E a.val y v
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldForms.Form`, `OAI.TamingCompatibility.ManifoldForms.Model` and `OAI.TamingCompatibility.ManifoldForms.Space` (definitions bundle `OAIQ239Tc002` of this split); `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.ManifoldForms.smoothForms` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add` and `OAI.TamingCompatibility.GeometricHilbert.preL2Module` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.hodgeLaplacian` (definitions bundle `OAIQ239Tc018` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.framePairing`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalResidual`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernelTestSlice` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeInputInitial.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive)

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
lemma leading_time_primitive (y : X) (v : FrameSpace A)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in (0:ℝ)..t,
      kernelTestSlice A J α ht E (globalResidual J α ht A E) y v a.val s -
      kernelTestSlice A J α ht E (globalLeading J α ht A E) y v
        (hodgeLaplacian A J α hs ht a).val s) =
    kernelTestSlice A J α ht E (globalLeading J α ht A E) y v a.val t -
      framePairing A J α ht E a.val y v := by
  sorry

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
