-- Prove2me | Theorems.Thm_GlobalTheory_FullLevel_Uniq_ev_nsmul
-- name    : GlobalTheory.FullLevel.Uniq.ev_nsmul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:33:48.694642+00:00
-- url     : https://prove2.me/theorems/6554c818-36db-4f38-94d2-a0a98071d06d
-- title:
--   Uniq: ev nsmul
-- statement:
--   The Uniq construction uses the ev nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullSymplecticLevelStructureUniqueOfLevels.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFullSymplecticLevelStructureUniqueOfLevels.lean#L58-L61

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
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
  {N : ℕ} {z : kˣ} {ev : D.La → Q}

theorem GlobalTheory.FullLevel.Uniq.ev_nsmul (h : IsSympLevel D act e N z ev) (n : ℕ) (a : D.La) : ev (n • a) = ev a ^ n := by sorry
