-- Prove2me | Theorems.Thm_GlobalTheory_FullLevel_bar_bar
-- name    : GlobalTheory.FullLevel.bar_bar
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:09.813912+00:00
-- url     : https://prove2.me/theorems/1384e730-f617-46b5-a4b2-b05e7187c0e2
-- title:
--   Full Level: bar bar
-- statement:
--   The Full Level construction uses the bar bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFullSymplecticLevelStructureOfTateIso.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFullSymplecticLevelStructureOfTateIso.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.FullLevel.bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by sorry
