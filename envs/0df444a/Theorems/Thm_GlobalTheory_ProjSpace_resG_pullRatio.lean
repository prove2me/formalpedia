-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_resG_pullRatio
-- name    : GlobalTheory.ProjSpace.resG_pullRatio
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:30.355018+00:00
-- url     : https://prove2.me/theorems/96caf048-a7bc-45e4-b90d-585efb8a45ca
-- title:
--   Proj Space: res G pull Ratio
-- statement:
--   The Proj Space construction uses the res G pull Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L64-L66

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
variable {φ : Y ⟶ PSpace R N} {W V : Y.Opens} {i j k : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {hj : W ≤ φ ⁻¹ᵁ chart R N j}

theorem GlobalTheory.ProjSpace.resG_pullRatio (h : V ≤ W) :
    resG Y h (pullRatio φ W i hi j) = pullRatio φ V i (h.trans hi) j := by sorry
