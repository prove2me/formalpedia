-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_isCoordFamily_pullRatio
-- name    : GlobalTheory.ProjSpace.isCoordFamily_pullRatio
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:49.937053+00:00
-- url     : https://prove2.me/theorems/1eb8e4f5-a50d-4eb8-8115-0ac7e6ebfcc4
-- title:
--   Proj Space: is Coord Family pull Ratio
-- statement:
--   The Proj Space construction uses the is Coord Family pull Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L223-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L223-L228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}

theorem GlobalTheory.ProjSpace.isCoordFamily_pullRatio (φ : Y ⟶ PSpace R N) :
    IsCoordFamily (fun i => φ ⁻¹ᵁ chart R N i) (fun i => pullRatio φ _ i le_rfl) := by sorry
