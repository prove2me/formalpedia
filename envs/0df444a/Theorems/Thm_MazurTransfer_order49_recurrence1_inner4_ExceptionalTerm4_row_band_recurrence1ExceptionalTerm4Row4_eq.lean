-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_ExceptionalTerm4_row_band_recurrence1ExceptionalTerm4Row4_eq
-- name    : MazurTransfer.order49_recurrence1_inner4_ExceptionalTerm4_row_band_recurrence1ExceptionalTerm4Row4_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T10:22:10.741985+00:00
-- url     : https://prove2.me/theorems/7fcab1e7-f967-4861-a873-517d9e6457ee
-- title:
--   First recurrence ExceptionalTerm4: recurrence1ExceptionalTerm4Row4 eq
-- statement:
--   Let $U_i,V_i\in\mathbb{Q}[t]$ be the two original row or band polynomials specified in the formal statement for ExceptionalTerm4 in the first order-49 pseudo-division recurrence. Establish the unconditional identity
--   \[U_i=V_i.\]
--   This identity supplies one exact original row or band in the product certificate and preserves every original coefficient.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1ExceptionalTerm4.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row4_eq. The original normalized identity timed out after300s; its original row and band kernel dependencies now select smaller closed proof contracts. Exact complete original Lean AST signature and proof-command ranges are retained, with checked resolved-reference changes only. Newly exported pure helper values are independently kernel-reflexivity compared against actual original constants. No proof is included in that data package. Apache-2.0 attribution is preserved. Named downstream consumers: normalized coefficient 4 exact certificate, first-recurrence certificate, bounded-resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1ExceptionalTerm4ExactRowBandDataPart4
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner4_ExceptionalTerm4_row_band_recurrence1ExceptionalTerm4Row4_eq :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalBlock4 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34 =
      MazurTransfer.Order49Recurrence1ExceptionalTerm4ExactRowBandData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4Row4 := by sorry
