-- Prove2me | Theorems.Thm_GlobalTheory_Ex_TateInh_not_inG
-- name    : GlobalTheory.Ex.TateInh.not_inG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:01.042038+00:00
-- url     : https://prove2.me/theorems/8e60eeca-8987-54b4-abde-f284589f5077
-- title:
--   Tate Inh: not in G
-- statement:
--   The Tate Inh construction uses the not in G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L500-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L500-L504

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

theorem GlobalTheory.Ex.TateInh.not_inG (r : Oˣ) : ¬ (tate (r ^ 3)).InG (tateQ r 3 1) := by sorry
