-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_pullRatio_of_eq
-- name    : GlobalTheory.ProjSpace.pullRatio_of_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:25.35993+00:00
-- url     : https://prove2.me/theorems/ee484e53-3d8f-4ef0-9505-5bd6043e5234
-- title:
--   Proj Space: pull Ratio of eq
-- statement:
--   The Proj Space construction uses the pull Ratio of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L92-L95

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

theorem GlobalTheory.ProjSpace.pullRatio_of_eq {ψ : Y ⟶ PSpace R N} (h : φ = ψ) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (hi' : W ≤ ψ ⁻¹ᵁ chart R N i) : pullRatio φ W i hi j = pullRatio ψ W i hi' j := by sorry
