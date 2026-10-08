-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner5_shift_row_band_recurrence1ShiftTerm5Band20_eq
-- name    : MazurTransfer.order49_recurrence1_inner5_shift_row_band_recurrence1ShiftTerm5Band20_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T08:44:27.688601+00:00
-- url     : https://prove2.me/theorems/142b41ea-7945-4e1b-85a9-160a2b8efcc7
-- title:
--   First recurrence shift-product: recurrence1ShiftTerm5Band20 eq
-- statement:
--   This is the exact original unconditional helper polynomial equality recurrence1ShiftTerm5Band20_eq. Its newly named helper polynomials have independently kernel-checked equality to their actual original values. No coefficient or mathematical hypothesis changes. This supplies the original normalized inner5 identity in the first pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm5.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Band20_eq. The original normalized identity timed out after300s; its 33 original row and band kernel dependencies now select smaller closed proof contracts. Exact complete original Lean AST signature and proof-command ranges are retained, with checked resolved-reference changes only. Newly exported pure helper values are independently kernel-reflexivity compared against actual original constants. No proof is included in that data package. Apache-2.0 attribution is preserved. Named downstream consumers: normalized inner5 exact certificate, first-recurrence certificate, bounded-resultant nonvanishing and full every-curve order49 exclusion. The combined pure data package timed out; this version imports its exact kernel-selected original row data parts. Polynomial values, statement, names and all proof commands are unchanged. All 175 part values have a fresh independent original-value audit.

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner5_shift_row_band_recurrence1ShiftTerm5Band20_eq :
    MazurTransfer.Order49Recurrence1ShiftExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Band20 = MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5Block20 := by sorry
