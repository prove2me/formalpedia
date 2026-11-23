-- Prove2me | Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq
-- name    : GlobalTheory.ValuedPrincipal.exists_val_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:44.57923+00:00
-- url     : https://prove2.me/theorems/49c64bf9-b4dc-417d-985b-3ee08f8aaab7
-- title:
--   Valued Principal: exists val eq
-- statement:
--   The Valued Principal construction uses the exists val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L7-L19

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

theorem GlobalTheory.ValuedPrincipal.exists_val_eq {x : F} (hx : x ≠ 0) :
    ∃ r : ℚ, v x = (r : WithTop ℚ) ∧ v x⁻¹ = ((-r : ℚ) : WithTop ℚ) := by sorry
