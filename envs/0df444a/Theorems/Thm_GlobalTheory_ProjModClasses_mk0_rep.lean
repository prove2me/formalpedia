-- Prove2me | Theorems.Thm_GlobalTheory_ProjModClasses_mk0_rep
-- name    : GlobalTheory.ProjModClasses.mk0_rep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:15.945635+00:00
-- url     : https://prove2.me/theorems/fe9dde47-6290-422e-aa77-362339f0f0e5
-- title:
--   Proj Mod Classes: mk0 rep
-- statement:
--   The Proj Mod Classes construction uses the mk0 rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinRepsProjectiveFinrankLeNumberField.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFinRepsProjectiveFinrankLeNumberField.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.ProjModClasses
variable {R : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]

theorem GlobalTheory.ProjModClasses.mk0_rep (c : ClassGroup R) : ClassGroup.mk0 ⟨rep c, rep_mem c⟩ = c := by sorry
