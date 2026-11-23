-- Prove2me | Theorems.Thm_GlobalTheory_FrameBiextId_sq_ac
-- name    : GlobalTheory.FrameBiextId.sq_ac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:25.591411+00:00
-- url     : https://prove2.me/theorems/1031665a-3e30-40fa-9d13-0f3331f2d6a9
-- title:
--   Frame Biext Id: sq ac
-- statement:
--   The Frame Biext Id construction uses the sq ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FormalPointSubstitutionSeriesValueAtTwoPoints.lean#L97-L105

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

theorem GlobalTheory.FrameBiextId.sq_ac (b : Fin n → Q k d l) (A : Q k d 1) (u : Q k d n) : sq b (ac A u) = ac A (sq b u) := by sorry
