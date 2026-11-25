-- Prove2me | Theorems.Thm_GlobalTheory_SympQ_pushQ_mk
-- name    : GlobalTheory.SympQ.pushQ_mk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:03.389967+00:00
-- url     : https://prove2.me/theorems/5f5bade2-879e-59a9-b904-fa3f9c2980d6
-- title:
--   Symp Q: push Q mk
-- statement:
--   The Symp Q construction uses the push Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WpQTrivRight.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WpQTrivRight.lean#L57-L58

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

theorem GlobalTheory.SympQ.pushQ_mk (M n : ℕ) (p : N.QT M) :
    pushQ N M n (QuotientGroup.mk p) = QuotientGroup.mk (pushRep N M n p) := by sorry
