-- Prove2me | Theorems.Thm_GlobalTheory_Ex_TateInh_tateMatch_onB
-- name    : GlobalTheory.Ex.TateInh.tateMatch_onB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:53.180148+00:00
-- url     : https://prove2.me/theorems/925ca391-aa82-4734-a38d-b140f73cfa86
-- title:
--   Tate Inh: tate Match on B
-- statement:
--   The Tate Inh construction uses the tate Match on B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L523-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L523-L524

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

theorem GlobalTheory.Ex.TateInh.tateMatch_onB {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) (hn : Odd n) :
    (tateMatch q n hn).OnB (isoRefl _).toIso := by sorry
