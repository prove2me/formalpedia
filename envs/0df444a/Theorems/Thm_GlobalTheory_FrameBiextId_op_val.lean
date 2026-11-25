-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_op_val
-- name    : GlobalTheory.FrameBiextId.op_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:25.236922+00:00
-- url     : https://prove2.me/theorems/c0b13c5e-bdb1-4c3e-9e19-4f07f19ad984
-- title:
--   Frame Biext Id: op val
-- statement:
--   The Frame Biext Id construction uses the op val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L132-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FormalPointSubstitutionSeriesValueAtTwoPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}

theorem GlobalTheory.FrameBiextId.op_val (F : Q k d 2) (u v : Q k d n) : (op F u v).1 = addOf F.1 u.1 v.1 := by sorry
