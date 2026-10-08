-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner2_ShiftTerm2_row_band_recurrence1ShiftTerm2Band14_eq
-- name    : MazurTransfer.order49_recurrence1_inner2_ShiftTerm2_row_band_recurrence1ShiftTerm2Band14_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T10:19:10.712984+00:00
-- url     : https://prove2.me/theorems/d3e2fa17-3a8f-4297-81ab-57f3021536fa
-- title:
--   First recurrence ShiftTerm2: recurrence1ShiftTerm2Band14 eq
-- statement:
--   Let $U_i,V_i\in\mathbb{Q}[t]$ be the two original row or band polynomials specified in the formal statement for ShiftTerm2 in the first order-49 pseudo-division recurrence. Establish the unconditional identity
--   \[U_i=V_i.\]
--   This identity supplies one exact original row or band in the product certificate and preserves every original coefficient.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm2.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Band14_eq. The original normalized identity timed out after300s; its original row and band kernel dependencies now select smaller closed proof contracts. Exact complete original Lean AST signature and proof-command ranges are retained, with checked resolved-reference changes only. Newly exported pure helper values are independently kernel-reflexivity compared against actual original constants. No proof is included in that data package. Apache-2.0 attribution is preserved. Named downstream consumers: normalized coefficient 2 exact certificate, first-recurrence certificate, bounded-resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner2ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm2ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner2_ShiftTerm2_row_band_recurrence1ShiftTerm2Band14_eq :
    MazurTransfer.Order49Recurrence1ShiftTerm2ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Band14 = MazurTransfer.Order49Recurrence1Inner2ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2Block14 := by sorry
