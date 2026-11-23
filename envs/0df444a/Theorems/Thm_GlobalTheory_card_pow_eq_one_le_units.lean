-- Prove2me | Theorems.Thm_GlobalTheory_card_pow_eq_one_le_units
-- name    : GlobalTheory.card_pow_eq_one_le_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:41.471692+00:00
-- url     : https://prove2.me/theorems/fbde0885-d399-484d-bdb4-235315b73610
-- title:
--   Global Theory: card pow eq one le units
-- statement:
--   The Global Theory construction uses the card pow eq one le units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean#L39-L46

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.card_pow_eq_one_le_units {M : Type*} [Monoid M] [Finite M] {d : ℕ} (hd : 0 < d) :
    Nat.card {x : M // x ^ d = 1} ≤ Nat.card {x : Mˣ // x ^ d = 1} := by sorry
