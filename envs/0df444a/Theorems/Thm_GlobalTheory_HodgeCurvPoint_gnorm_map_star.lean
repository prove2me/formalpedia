-- Prove2me | Theorems.Thm_GlobalTheory_HodgeCurvPoint_gnorm_map_star
-- name    : GlobalTheory.HodgeCurvPoint.gnorm_map_star
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:54.307792+00:00
-- url     : https://prove2.me/theorems/3f7321db-9beb-45ec-951c-8feca4225613
-- title:
--   Hodge Curv Point: gnorm map star
-- statement:
--   The Hodge Curv Point construction uses the gnorm map star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L45-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}

theorem GlobalTheory.HodgeCurvPoint.gnorm_map_star (M : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℂ) :
    gnorm (M.map ofReal) (star u) = gnorm (M.map ofReal) u := by sorry
