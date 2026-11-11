-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_kernel_leading_pairing_initial
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:40.421925+00:00
-- url     : https://prove2.me/theorems/475f2bfa-efd1-4ed6-bafa-83b5826ac632
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeInputInitial.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeInputInitial.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory`, `open scoped Manifold ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma kernel_leading_pairing_initial (y : X) (v : FrameSpace A)
--       (a : TwoForm X) (ha : IsSmooth a) :
--       Tendsto (fun t : ℝ => ∫ x, framePairing A J α ht E a x
--         (globalLeading J α ht A E t x y v) ∂geometricVolume A J α)
--         (𝓝[>] 0) (𝓝 (framePairing A J α ht E a y v))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` and `OAI.TamingCompatibility.ManifoldVolume.geometricVolume` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.FrameSpace` (definitions bundle `OAIQ239Tc017` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.framePairing`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalLeading` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_L2_of_bounds` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.leading_time_primitive` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeInputInitial.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.kernel_leading_pairing_initial)

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
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma kernel_leading_pairing_initial (y : X) (v : FrameSpace A)
    (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ x, framePairing A J α ht E a x
      (globalLeading J α ht A E t x y v) ∂geometricVolume A J α)
      (𝓝[>] 0) (𝓝 (framePairing A J α ht E a y v)) := by
  sorry

attribute [local irreducible] framePairing globalLeading globalResidual

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end
