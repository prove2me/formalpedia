-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_Model_nilpotent_form
-- name    : GlobalTheory.ProjSpace.Model.nilpotent_form
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:34.225928+00:00
-- url     : https://prove2.me/theorems/18ef386f-6c2b-5861-a66a-e066b2388aff
-- title:
--   Model: nilpotent form
-- statement:
--   The Model construction uses the nilpotent form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L211-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsFormOfEqRatioPowMul.lean#L211-L221

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

theorem GlobalTheory.ProjSpace.Model.nilpotent_form (h : (C 2 * X 0 : MvPolynomial (Fin 2) (ZMod 4)).IsHomogeneous 1) :
    formSec 1 _ h ≠ formSec 1 0 (isHomogeneous_zero _ _ 1) ∧ nonzeroLocus (formSec 1 _ h) = ⊥ := by sorry
