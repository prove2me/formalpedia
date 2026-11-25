-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_mem_tz
-- name    : GlobalTheory.SatakeWeyl.Heis.mem_tz
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:09.124808+00:00
-- url     : https://prove2.me/theorems/b2225558-6715-5ea9-8123-a6aec5a893fb
-- title:
--   Heis: mem tz
-- statement:
--   The Heis construction uses the mem tz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryRankThreeRootIndexOfCards.lean#L119-L120

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

theorem GlobalTheory.SatakeWeyl.Heis.mem_tz (y : L) : y ∈ (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔
    y ∈ intL L ∧ σ y + y = 0 := by sorry
