-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_Model_formSec_X_f
-- name    : GlobalTheory.ProjSpace.Model.formSec_X_f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:40.564824+00:00
-- url     : https://prove2.me/theorems/17c98866-1476-45ac-a9f4-e754f0c74487
-- title:
--   Model: form Sec X f
-- statement:
--   The Model construction uses the form Sec X f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L223-L226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}

theorem GlobalTheory.ProjSpace.Model.formSec_X_f (k : Fin (N + 1)) (j : PUnit → Fin (N + 1)) :
    (formSec 1 (X k) (isHomogeneous_X R k)).f j =
      resG _ (On_U R N 1 j).le ((coord R N k).f (j PUnit.unit)) := by sorry
