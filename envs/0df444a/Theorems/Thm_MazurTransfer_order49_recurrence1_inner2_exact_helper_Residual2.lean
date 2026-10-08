-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner2_exact_helper_Residual2
-- name    : MazurTransfer.order49_recurrence1_inner2_exact_helper_Residual2
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T09:31:33.897283+00:00
-- url     : https://prove2.me/theorems/ec4f79f7-a208-4f53-9aa5-5f2e84f5cc5f
-- title:
--   First recurrence coefficient 2: Residual2
-- statement:
--   Establish the exact original unconditional polynomial equality recurrence1Residual2 over the rational polynomial ring. All polynomial values are independently kernel compared with the pinned originals. No hypothesis or coefficient is changed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual2. Apache-2.0 attribution preserved. Exact original complete Lean AST signature and resolved references retain every operand. Newly exported values have independent kernel-reflexivity audits, and the original theorem type is independently kernel compared with the copied equality before publication. Logical equivalence of a generic certificate is claimed, not definitional equality; its definition contains no constructed equality proof. Named downstream consumers: unchanged normalized coefficient 2, first recurrence, bounded resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner2ExactHelperDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner2ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner2ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner2ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner2_exact_helper_Residual2 :
    MazurTransfer.Order49Recurrence1Inner2ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left2 =
      MazurTransfer.Order49Recurrence1Inner2ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm2 +
      MazurTransfer.Order49Recurrence1Inner2ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm2 +
      MazurTransfer.Order49Recurrence1Inner2ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm2 := by sorry
