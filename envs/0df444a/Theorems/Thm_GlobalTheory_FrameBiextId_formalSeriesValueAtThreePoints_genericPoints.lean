-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_formalSeriesValueAtThreePoints_genericPoints
-- name    : GlobalTheory.FrameBiextId.formalSeriesValueAtThreePoints_genericPoints
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:10.481934+00:00
-- url     : https://prove2.me/theorems/0fe8ed51-755f-5bec-a92d-29220b94041e
-- title:
--   Frame Biext Id: formal Series Value At Three Points generic Points
-- statement:
--   The Frame Biext Id construction uses the formal Series Value At Three Points generic Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L88-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L88-L93

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

theorem GlobalTheory.FrameBiextId.formalSeriesValueAtThreePoints_genericPoints (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by sorry
