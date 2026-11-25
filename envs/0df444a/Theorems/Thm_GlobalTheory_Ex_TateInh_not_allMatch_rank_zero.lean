-- Prove2me | Theorems.Thm_GlobalTheory_Ex_TateInh_not_allMatch_rank_zero
-- name    : GlobalTheory.Ex.TateInh.not_allMatch_rank_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:54.598093+00:00
-- url     : https://prove2.me/theorems/87f15c78-eb37-5474-9e39-c681df1d4e9d
-- title:
--   Tate Inh: not all Match rank zero
-- statement:
--   The Tate Inh construction uses the not all Match rank zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L430-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L430-L442

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh

theorem GlobalTheory.Ex.TateInh.not_allMatch_rank_zero : ¬ AllMatch fun {_} _ {N} {_} {_} _ _ _ => Subsingleton N.X := by sorry
