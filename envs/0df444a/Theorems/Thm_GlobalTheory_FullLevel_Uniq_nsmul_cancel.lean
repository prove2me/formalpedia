-- Prove2me | Theorems.Thm_GlobalTheory_FullLevel_Uniq_nsmul_cancel
-- name    : GlobalTheory.FullLevel.Uniq.nsmul_cancel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:04.151894+00:00
-- url     : https://prove2.me/theorems/bf60b4af-ca17-478d-87b5-eda118cd76e0
-- title:
--   Uniq: nsmul cancel
-- statement:
--   The Uniq construction uses the nsmul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullSymplecticLevelStructureUniqueOfLevels.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullSymplecticLevelStructureUniqueOfLevels.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
open GlobalTheory GlobalTheory.FullLevel GlobalTheory.FullLevel.Uniq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.FullLevel.Uniq.nsmul_cancel {n : ℕ} (hn : n ≠ 0) {x y : D.La} (h : n • x = n • y) : x = y := by sorry
