-- Prove2me | Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq_int
-- name    : GlobalTheory.ValuedPrincipal.exists_val_eq_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:50.42244+00:00
-- url     : https://prove2.me/theorems/52015989-0ff9-4d14-8a6d-ea328c35a6ce
-- title:
--   Valued Principal: exists val eq int
-- statement:
--   The Valued Principal construction uses the exists val eq int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L21-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem GlobalTheory.ValuedPrincipal.exists_val_eq_int {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) (n : ℤ) :
    ∃ y : F, y ≠ 0 ∧ v y = ((n : ℚ) : WithTop ℚ) := by sorry
