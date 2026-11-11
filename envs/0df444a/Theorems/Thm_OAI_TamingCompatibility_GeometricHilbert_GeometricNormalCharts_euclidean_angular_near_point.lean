-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_euclidean_angular_near_point
-- name    : OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:19.286408+00:00
-- url     : https://prove2.me/theorems/9f6e2200-1c5f-498e-a8a3-e87a95f2985b
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/EuclideanAngularNearPoint.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/EuclideanAngularNearPoint.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts`, with `open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory`, `open Hermitian UnitaryFrame PlaneVariation`, `open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal`):
--
--   ```lean
--   lemma euclidean_angular_near_point (p : A.centers) :
--       ∃ C B L ρ : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ 0 < L ∧ 0 < ρ ∧
--         ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ uv : UnitPair J α hs ht,
--         euclideanAngularNear A J α hs ht E s p uv ≤ C*angularNear A J α hs ht E (L*s) p uv +
--           B*s^2*(euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ)) uv
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.UnitPair`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.angularNear`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanAngularNear`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclideanNearSet` and `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ParametrixData.source` (definitions bundle `OAIQ239Tc021` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_euclidean_angular_profile` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/EuclideanAngularNearPoint.lean (declaration OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point)

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

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel
include hE in
omit [SecondCountableTopology X] in
lemma euclidean_angular_near_point (p : A.centers) :
    ∃ C B L ρ : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ 0 < L ∧ 0 < ρ ∧
      ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ uv : UnitPair J α hs ht,
      euclideanAngularNear A J α hs ht E s p uv ≤ C*angularNear A J α hs ht E (L*s) p uv +
        B*s^2*(euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ)) uv := by
  sorry
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end
