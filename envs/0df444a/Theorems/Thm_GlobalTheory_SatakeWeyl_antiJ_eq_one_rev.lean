-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_antiJ_eq_one_rev
-- name    : GlobalTheory.SatakeWeyl.antiJ_eq_one_rev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:50.17483+00:00
-- url     : https://prove2.me/theorems/22ed6688-06c5-4caf-872f-e31c230fb355
-- title:
--   Satake Weyl: anti J eq one rev
-- statement:
--   The Satake Weyl construction uses the anti J eq one rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryUnipotentRadicalSplittingOfLeviPart.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryUnipotentRadicalSplittingOfLeviPart.lean#L9-L13

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPart
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl

theorem GlobalTheory.SatakeWeyl.antiJ_eq_one_rev {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i.rev = j then 1 else 0 := by sorry
