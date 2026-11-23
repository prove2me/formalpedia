-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_mdifferentiableAt_pi_of_forall
-- name    : GlobalTheory.AffinePoints.mdifferentiableAt_pi_of_forall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:20.490797+00:00
-- url     : https://prove2.me/theorems/39fbac79-9626-4345-8cfa-a79ec7a41b32
-- title:
--   Affine Points: mdifferentiable At pi of forall
-- statement:
--   The Affine Points construction uses the mdifferentiable At pi of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L77-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
variable [CompleteSpace 𝕜]
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
omit [CompleteSpace 𝕜]

theorem GlobalTheory.AffinePoints.mdifferentiableAt_pi_of_forall {ι : Type*} [Fintype ι] {f : M → ι → 𝕜} {x : M}
    (hf : ∀ i, MDifferentiableAt I 𝓘(𝕜) (fun m => f m i) x) :
    MDifferentiableAt I 𝓘(𝕜, ι → 𝕜) f x := by sorry
