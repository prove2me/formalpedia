-- Prove2me | Theorems.Thm_GlobalTheory_ValuedPrincipal_val_pow_eq
-- name    : GlobalTheory.ValuedPrincipal.val_pow_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:50:22.681563+00:00
-- url     : https://prove2.me/theorems/17669978-1fcb-4647-b823-4aaa62b0245d
-- title:
--   Valued Principal: val pow eq
-- statement:
--   The Valued Principal construction uses the val pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L46-L54

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

theorem GlobalTheory.ValuedPrincipal.val_pow_eq {t : F} {r : ℚ} (h : v t = (r : WithTop ℚ)) (k : ℕ) :
    v (t ^ k) = (((k : ℚ) * r : ℚ) : WithTop ℚ) := by sorry
