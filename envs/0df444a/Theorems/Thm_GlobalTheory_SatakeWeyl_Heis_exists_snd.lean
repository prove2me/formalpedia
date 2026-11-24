-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_exists_snd
-- name    : GlobalTheory.SatakeWeyl.Heis.exists_snd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:06.346519+00:00
-- url     : https://prove2.me/theorems/6819dfa4-0403-47dc-97c6-db3e3ef0ad16
-- title:
--   Heis: exists snd
-- statement:
--   The Heis construction uses the exists snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L122-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L122-L136

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.SatakeWeyl.Heis.exists_snd {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {x : L} (hx : x ∈ intL L) :
    ∃ y ∈ intL L, y + σ y + x * σ x = 0 := by sorry
