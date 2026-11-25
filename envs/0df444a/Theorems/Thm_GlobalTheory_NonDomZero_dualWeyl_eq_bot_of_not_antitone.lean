-- Prove2me | Theorems.Thm_GlobalTheory_NonDomZero_dualWeyl_eq_bot_of_not_antitone
-- name    : GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:47:32.970859+00:00
-- url     : https://prove2.me/theorems/0a753627-9411-5957-acec-1bcdf9364da4
-- title:
--   Non Dom Zero: dual Weyl eq bot of not antitone
-- statement:
--   The Non Dom Zero construction uses the dual Weyl eq bot of not antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualWeylEqBotOfNotAntitone.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualWeylEqBotOfNotAntitone.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualWeylEqBotOfNotAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonDomZero

theorem GlobalTheory.NonDomZero.dualWeyl_eq_bot_of_not_antitone :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by sorry
