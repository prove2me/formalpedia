-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence4_fixed_value_leadingSquare
-- name    : MazurTransfer.order49_recurrence4_fixed_value_leadingSquare
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T12:47:49.69236+00:00
-- url     : https://prove2.me/theorems/3f30527e-e08e-4b7f-b8dd-113cb69124dd
-- title:
--   Fourth recurrence: exact shared fixed value leadingSquare
-- statement:
--   The shared integer-list convolution or combination leadingSquare equals precisely its fixed integer coefficient list. This is an unconditional equality of complete lists, with no coefficient omitted or hypothesis added.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0. The candidate list has an independently checked closed ordinary kernel proof against the exact original total integer-list operation. This value is now a separately registered obligation so the complete original scalar certificate can reuse the equality without rechecking every shared convolution in one job. Named downstream consumers: unchanged fourth-recurrence integer scalar identities, all three original rational-polynomial scalar statements, recurrence4 and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence4FixedIntegerIntermediatesPart0

theorem MazurTransfer.order49_recurrence4_fixed_value_leadingSquare : MazurTransfer.Order49Recurrence4DenseCandidate.leadingSquare = MazurTransfer.Order49Recurrence4DenseCandidate.Fixed.leadingSquare := by sorry
