-- Prove2me | Theorems.Thm_GlobalTheory_Ex_TateInh_tateMatch_not_B
-- name    : GlobalTheory.Ex.TateInh.tateMatch_not_B
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:56.136793+00:00
-- url     : https://prove2.me/theorems/9a60f3de-c761-406c-ba0e-73012844f4b9
-- title:
--   Tate Inh: tate Match not B
-- statement:
--   The Tate Inh construction uses the tate Match not B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L454-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L454-L459

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

theorem GlobalTheory.Ex.TateInh.tateMatch_not_B (r : ℂˣ) : ¬ (tateMatch (r ^ 3 ^ 1) 3 (by decide)).B (AddEquiv.neg ℤ) := by sorry
