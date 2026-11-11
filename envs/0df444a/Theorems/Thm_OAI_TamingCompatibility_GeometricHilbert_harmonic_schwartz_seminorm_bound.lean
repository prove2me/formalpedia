-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_harmonic_schwartz_seminorm_bound
-- name    : OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:36:52.461353+00:00
-- url     : https://prove2.me/theorems/fb77d8bc-fce0-481a-b7fb-3d3a68411b11
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound` of [lean/OAI/Geometry/TamingCompatibility/Hodge/HarmonicSeminormBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HarmonicSeminormBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert`, with `open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set`, `open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv`):
--
--   ```lean
--   lemma harmonic_schwartz_seminorm_bound
--       (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (k n : ℕ) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
--         smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
--           (smoothL2 A J α hs ht true f.val) →
--         SchwartzMap.seminorm ℝ k n (F₀ h) ≤ C * ‖smoothL2 A J α hs ht true f.val‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.ManifoldLocalization.FiniteCharts` (definitions bundle `OAIQ239Tc003` of this split); `OAI.TamingCompatibility.GeometricChart.Data` and `OAI.TamingCompatibility.GeometricChart.Data.source` (definitions bundle `OAIQ239Tc011` of this split); `OAI.TamingCompatibility.GeometricHilbert.L2`, `OAI.TamingCompatibility.GeometricHilbert.PreL2`, `OAI.TamingCompatibility.GeometricHilbert.antiPre`, `OAI.TamingCompatibility.GeometricHilbert.preL2Add`, `OAI.TamingCompatibility.GeometricHilbert.preL2Inner`, `OAI.TamingCompatibility.GeometricHilbert.preL2Module`, `OAI.TamingCompatibility.GeometricHilbert.preL2Normed` and `OAI.TamingCompatibility.GeometricHilbert.smoothL2` (definitions bundle `OAIQ239Tc014` of this split); `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti` and `OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete` (definitions bundle `OAIQ239Tc034` of this split); `OAI.TamingCompatibility.AlmostComplexStructure`, `OAI.TamingCompatibility.IsSmooth`, `OAI.TamingCompatibility.Model`, `OAI.TamingCompatibility.Space`, `OAI.TamingCompatibility.Tames` and `OAI.TamingCompatibility.TwoForm` (the published bundle `Def_TamingCompatibility`).
--
--   **Used by.** The proofs of `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_logError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.Hermitian.scalarCorrection_sqrtError_estimate`, `OAI.TamingCompatibility.GeometricHilbert.closedLift_scalar_off_source`, `OAI.TamingCompatibility.GeometricHilbert.correctedDdc_off_source_compact`, `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_all_scales` and `OAI.TamingCompatibility.GeometricHilbert.scalarCorrection_local_estimates` of this split import it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HarmonicSeminormBound.lean (declaration OAI.TamingCompatibility.GeometricHilbert.harmonic_schwartz_seminorm_bound)

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

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

include hD in

lemma harmonic_schwartz_seminorm_bound
    (F₀ : antiPre A J α hs ht →ₗ[ℝ] 𝓢(E,F)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      SchwartzMap.seminorm ℝ k n (F₀ h) ≤ C * ‖smoothL2 A J α hs ht true f.val‖ := by
  sorry

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
end
