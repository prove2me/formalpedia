-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_resG_appLE
-- name    : GlobalTheory.ProjSpace.resG_appLE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:41.749374+00:00
-- url     : https://prove2.me/theorems/3e47bfb7-80a9-44d4-81e9-ae161f189597
-- title:
--   Proj Space: res G app LE
-- statement:
--   The Proj Space construction uses the res G app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IsClosedImmersionIffPullRatio.lean#L22-L25

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

theorem GlobalTheory.ProjSpace.resG_appLE (g : Z ⟶ Y) {U : Y.Opens} {V W : Z.Opens} (h : V ≤ g ⁻¹ᵁ U) (h' : W ≤ V)
    (a : Γ(Y, U)) :
    resG Z h' ((g.appLE U V h).hom a) = (g.appLE U W (h'.trans h)).hom a := by sorry
