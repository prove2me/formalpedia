-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_formalSeriesValueAtTwoPoints_genericPoints
-- name    : GlobalTheory.FrameBiextId.formalSeriesValueAtTwoPoints_genericPoints
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:29.0558+00:00
-- url     : https://prove2.me/theorems/559bd54e-9c45-40d7-ae58-c092d97db35b
-- title:
--   Frame Biext Id: formal Series Value At Two Points generic Points
-- statement:
--   The Frame Biext Id construction uses the formal Series Value At Two Points generic Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L81-L86

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

theorem GlobalTheory.FrameBiextId.formalSeriesValueAtTwoPoints_genericPoints (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by sorry
