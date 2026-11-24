-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_surjective_appLE_chart_iff
-- name    : GlobalTheory.ProjSpace.surjective_appLE_chart_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:04.358161+00:00
-- url     : https://prove2.me/theorems/fb28e2b9-88a4-4b72-a874-0a7dcec1ae85
-- title:
--   Proj Space: surjective app LE chart iff
-- statement:
--   The Proj Space construction uses the surjective app LE chart iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L313-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L313-L318

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

theorem GlobalTheory.ProjSpace.surjective_appLE_chart_iff {φ : Y ⟶ PSpace R N} {W : Y.Opens} {i : Fin (N + 1)}
    (hi : W ≤ φ ⁻¹ᵁ chart R N i) :
    Function.Surjective (φ.appLE (chart R N i) W hi).hom ↔
      Function.Surjective (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) W).hom (pullRatio φ W i hi)) := by sorry
