-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner3_ShiftTerm3_row_band_recurrence1ShiftTerm3Band14_eq
-- name    : MazurTransfer.order49_recurrence1_inner3_ShiftTerm3_row_band_recurrence1ShiftTerm3Band14_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T10:14:40.406713+00:00
-- url     : https://prove2.me/theorems/caea2e4e-05b3-45d8-afa4-d82bfdba7abb
-- title:
--   First recurrence ShiftTerm3: recurrence1ShiftTerm3Band14 eq
-- statement:
--   Let $U_i,V_i\in\mathbb{Q}[t]$ be the two original row or band polynomials specified in the formal statement for ShiftTerm3 in the first order-49 pseudo-division recurrence. Establish the unconditional identity
--   \[U_i=V_i.\]
--   This identity supplies one exact original row or band in the product certificate and preserves every original coefficient.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm3.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Band14_eq. The original normalized identity timed out after300s; its original row and band kernel dependencies now select smaller closed proof contracts. Exact complete original Lean AST signature and proof-command ranges are retained, with checked resolved-reference changes only. Newly exported pure helper values are independently kernel-reflexivity compared against actual original constants. No proof is included in that data package. Apache-2.0 attribution is preserved. Named downstream consumers: normalized coefficient 3 exact certificate, first-recurrence certificate, bounded-resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner3ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart10
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart11
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart5
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart6
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart7
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart8
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm3ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner3_ShiftTerm3_row_band_recurrence1ShiftTerm3Band14_eq :
    MazurTransfer.Order49Recurrence1ShiftTerm3ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Band14 = MazurTransfer.Order49Recurrence1Inner3ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm3Block14 := by sorry
