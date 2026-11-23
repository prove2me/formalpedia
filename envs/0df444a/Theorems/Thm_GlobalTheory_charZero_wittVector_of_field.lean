-- Prove2me | Theorems.Thm_GlobalTheory_charZero_wittVector_of_field
-- name    : GlobalTheory.charZero_wittVector_of_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:59.505928+00:00
-- url     : https://prove2.me/theorems/4b8eb845-f724-44ba-8998-4b92cfa87f72
-- title:
--   Global Theory: char Zero witt Vector of field
-- statement:
--   The Global Theory construction uses the char Zero witt Vector of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsMultiplicativeLiftCharZero.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsMultiplicativeLiftCharZero.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsMultiplicativeLiftCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.charZero_wittVector_of_field (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by sorry
