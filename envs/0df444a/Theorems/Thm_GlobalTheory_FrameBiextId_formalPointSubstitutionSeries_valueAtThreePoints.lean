-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_formalPointSubstitutionSeries_valueAtThreePoints
-- name    : GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtThreePoints
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:27.035808+00:00
-- url     : https://prove2.me/theorems/ac6c2922-df8d-4020-b818-3340d91368cf
-- title:
--   Frame Biext Id: formal Point Substitution Series value At Three Points
-- statement:
--   The Frame Biext Id construction uses the formal Point Substitution Series value At Three Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L73-L79

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

theorem GlobalTheory.FrameBiextId.formalPointSubstitutionSeries_valueAtThreePoints (b : Fin n → Q k d l) (f : PS k 3 d) (u v w : Q k d n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by sorry
