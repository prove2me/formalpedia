-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_sb_sb
-- name    : GlobalTheory.FrameBiextId.sb_sb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:58.067004+00:00
-- url     : https://prove2.me/theorems/a1ab8174-54db-40b2-9ef3-8691acd08a0f
-- title:
--   Frame Biext Id: sb sb
-- statement:
--   The Frame Biext Id construction uses the sb sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L49-L56

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

theorem GlobalTheory.FrameBiextId.sb_sb {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by sorry
