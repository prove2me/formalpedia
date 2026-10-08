-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_ShiftTerm4_row_band_recurrence1ShiftTerm4Row9_eq
-- name    : MazurTransfer.order49_recurrence1_inner4_ShiftTerm4_row_band_recurrence1ShiftTerm4Row9_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T10:23:10.835229+00:00
-- url     : https://prove2.me/theorems/88a342a9-90c0-4fdf-9aee-e148217feb2b
-- title:
--   First recurrence ShiftTerm4: recurrence1ShiftTerm4Row9 eq
-- statement:
--   Let $U_i,V_i\in\mathbb{Q}[t]$ be the two original row or band polynomials specified in the formal statement for ShiftTerm4 in the first order-49 pseudo-division recurrence. Establish the unconditional identity
--   \[U_i=V_i.\]
--   This identity supplies one exact original row or band in the product certificate and preserves every original coefficient.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ShiftTerm4.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9_eq. The original normalized identity timed out after300s; its original row and band kernel dependencies now select smaller closed proof contracts. Exact complete original Lean AST signature and proof-command ranges are retained, with checked resolved-reference changes only. Newly exported pure helper values are independently kernel-reflexivity compared against actual original constants. No proof is included in that data package. Apache-2.0 attribution is preserved. Named downstream consumers: normalized coefficient 4 exact certificate, first-recurrence certificate, bounded-resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1ShiftTerm4ExactRowBandDataPart9
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner4_ShiftTerm4_row_band_recurrence1ShiftTerm4Row9_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26Block9 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23 =
      MazurTransfer.Order49Recurrence1ShiftTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4Row9 := by sorry
