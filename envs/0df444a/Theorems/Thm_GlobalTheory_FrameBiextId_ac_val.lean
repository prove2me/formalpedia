-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_ac_val
-- name    : GlobalTheory.FrameBiextId.ac_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:09.462676+00:00
-- url     : https://prove2.me/theorems/8675bd21-0da0-40dc-887f-3c6fae7c81cc
-- title:
--   Frame Biext Id: ac val
-- statement:
--   The Frame Biext Id construction uses the ac val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L121-L128

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

theorem GlobalTheory.FrameBiextId.ac_val (A : Q k d 1) (u : Q k d n) : (ac A u).1 = comp1 A.1 u.1 := by sorry
