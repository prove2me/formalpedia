-- Prove2me | Theorems.Thm_GlobalTheory_SympQ_wpQ_mk
-- name    : GlobalTheory.SympQ.wpQ_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:57.398047+00:00
-- url     : https://prove2.me/theorems/053e3657-75a7-5daa-b6f7-8dc1cd711e1b
-- title:
--   Symp Q: wp Q mk
-- statement:
--   The Symp Q construction uses the wp Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WpQTrivRight.lean#L74-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WpQTrivRight.lean#L74-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WpQTrivRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open GlobalTheory GlobalTheory.SympQ
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.SympQ.wpQ_mk (k : ℕ) (p q : N.QT k) : wpQ N k (QuotientGroup.mk p) (QuotientGroup.mk q) = N.wp p q := by sorry
