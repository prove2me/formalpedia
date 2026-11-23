-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_exists_isAlgebraicChart_of_away
-- name    : GlobalTheory.AffinePoints.exists_isAlgebraicChart_of_away
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:31.466109+00:00
-- url     : https://prove2.me/theorems/abef08fe-87bc-4ded-8810-d4a1bb90bfe9
-- title:
--   Affine Points: exists is Algebraic Chart of away
-- statement:
--   The Affine Points construction uses the exists is Algebraic Chart of away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L128-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasAlgebraicChartsOfIsStandardSmooth.lean#L128-L188

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

theorem GlobalTheory.AffinePoints.exists_isAlgebraicChart_of_away (s : A) (B : Type*) [CommRing B] [Algebra 𝕜 B]
    [Algebra A B] [IsScalarTower 𝕜 A B] [IsLocalization.Away s B]
    [Algebra.IsStandardSmoothOfRelativeDimension d 𝕜 B] (p : A →ₐ[𝕜] 𝕜) (hp : p s ≠ 0) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), IsAlgebraicChart e ∧ p ∈ e.source := by sorry
