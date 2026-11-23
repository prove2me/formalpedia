-- Prove2me | Theorems.Thm_GlobalTheory_card_pow_eq_one_le_of_isCyclic_units
-- name    : GlobalTheory.card_pow_eq_one_le_of_isCyclic_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:37.32791+00:00
-- url     : https://prove2.me/theorems/37fdbe1c-7fde-4c31-b14c-c55a61b0eb82
-- title:
--   Global Theory: card pow eq one le of is Cyclic units
-- statement:
--   The Global Theory construction uses the card pow eq one le of is Cyclic units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPowEqOneLeOfIsCyclicUnits.lean#L48-L50

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

theorem GlobalTheory.card_pow_eq_one_le_of_isCyclic_units (n : ℕ) [NeZero n] [IsCyclic (ZMod n)ˣ] {d : ℕ}
    (hd : 0 < d) : Nat.card {x : ZMod n // x ^ d = 1} ≤ d := by sorry
