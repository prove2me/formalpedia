-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_geometric_smooth_inverse
-- name    : OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:36:57.028195+00:00
-- url     : https://prove2.me/theorems/a31bf32e-21ed-4622-b491-8f47712bd4b0
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse` of [lean/OAI/Geometry/TamingCompatibility/DifferentialForms/SmoothGeometricInverse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/SmoothGeometricInverse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set`, `open scoped Manifold ContDiff RealInnerProductSpace`):
--
--   ```lean
--   theorem geometric_smooth_inverse :
--       FiniteDimensional ℝ (harmonicAnti A J α hs ht) ∧
--         ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
--           (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
--             ⟪f - (harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
--           (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
--           (∀ f ∈ harmonicAnti A J α hs ht, G f = 0) ∧
--           (∀ f : antiPre A J α hs ht, ∃ b : antiPre A J α hs ht,
--             antiToEnergy A J α hs ht b = G (smoothL2 A J α hs ht true f.val))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.antiEnergy`, `OAI.TamingCompatibility.GeometricHilbert.antiToEnergy` and `OAI.TamingCompatibility.GeometricHilbert.energyInclusion` (definitions bundle `OAIQ239Tc025` of this split); `OAI.TamingCompatibility.GeometricHilbert.weakDelta` (definitions bundle `OAIQ239Tc028` of this split); `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti` and `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete` (definitions bundle `OAIQ239Tc034` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.exists_closed_lift_hodge_bound`, `OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound`, `OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate`, `OAI.TamingCompatibility.separating_probability_atlas_defect` and `OAI.TamingCompatibility.separating_probability_local_quadratic` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/DifferentialForms/SmoothGeometricInverse.lean (declaration OAI.TamingCompatibility.GeometricHilbert.geometric_smooth_inverse)

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034

section

attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.HilbertSobolev.localSolutionSpace_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

theorem geometric_smooth_inverse :
    FiniteDimensional ℝ (harmonicAnti A J α hs ht) ∧
      ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
        (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
          ⟪f - (harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
        (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
        (∀ f ∈ harmonicAnti A J α hs ht, G f = 0) ∧
        (∀ f : antiPre A J α hs ht, ∃ b : antiPre A J α hs ht,
          antiToEnergy A J α hs ht b = G (smoothL2 A J α hs ht true f.val)) := by
  sorry

end TamingCompatibility.GeometricHilbert

end

end OAI
end
