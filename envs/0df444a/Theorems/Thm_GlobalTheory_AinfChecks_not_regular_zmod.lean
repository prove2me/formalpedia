-- Prove2me | Theorems.Thm_GlobalTheory_AinfChecks_not_regular_zmod
-- name    : GlobalTheory.AinfChecks.not_regular_zmod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:37.378731+00:00
-- url     : https://prove2.me/theorems/57eb7947-83be-529b-9463-1d58fdba4586
-- title:
--   Ainf Checks: not regular zmod
-- statement:
--   The Ainf Checks construction uses the not regular zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean#L45-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.AinfChecks

theorem GlobalTheory.AinfChecks.not_regular_zmod (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : ZMod p)) (_ : IsAdicComplete (span {((p : ℕ) : ZMod p)}) (ZMod p)),
      ¬ RegularStatement p (ZMod p) := by sorry
