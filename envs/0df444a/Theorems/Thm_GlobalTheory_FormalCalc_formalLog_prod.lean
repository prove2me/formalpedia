-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_formalLog_prod
-- name    : GlobalTheory.FormalCalc.formalLog_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:34:19.61939+00:00
-- url     : https://prove2.me/theorems/8de566db-047e-45c9-a261-385c36c7341b
-- title:
--   Formal Calc: formal Log prod
-- statement:
--   The Formal Calc construction uses the formal Log prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FormalExpMulFormalExpNeg.lean#L108-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]

theorem GlobalTheory.FormalCalc.formalLog_prod {κ : Type*} (s : Finset κ) {g : κ → MvPowerSeries σ A}
    (hg : ∀ k ∈ s, constantCoeff (g k) = 1) :
    formalLog (∏ k ∈ s, g k) = ∑ k ∈ s, formalLog (g k) := by sorry
