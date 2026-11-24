-- Prove2me | Theorems.Thm_GlobalTheory_DI_Dtot_Dtot
-- name    : GlobalTheory.DI.Dtot_Dtot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:26.395809+00:00
-- url     : https://prove2.me/theorems/d48308f1-8615-424f-bf61-b480f05da94c
-- title:
--   DI: Dtot Dtot
-- statement:
--   The DI construction uses the Dtot Dtot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L52-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L52-L71

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

theorem GlobalTheory.DI.Dtot_Dtot (d : E →+ E) (hd : ∀ x, d (d x) = 0) (c : Finset ι → E) :
    Dtot d (Dtot d c) = 0 := by sorry
