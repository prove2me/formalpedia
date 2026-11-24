-- Prove2me | Theorems.Thm_GlobalTheory_DI_Dtot_add
-- name    : GlobalTheory.DI.Dtot_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:27.007389+00:00
-- url     : https://prove2.me/theorems/60f3177b-5071-49dc-ab55-4214cce54d8c
-- title:
--   DI: Dtot add
-- statement:
--   The DI construction uses the Dtot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L42-L45

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem GlobalTheory.DI.Dtot_add (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c + c') = Dtot d c + Dtot d c' := by sorry
