-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_Residual4
-- name    : MazurTransfer.order49_recurrence1_inner4_exact_helper_Residual4
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T09:30:39.394991+00:00
-- url     : https://prove2.me/theorems/7c1a4069-52c0-4a1f-8b79-2ae420feff53
-- title:
--   First recurrence coefficient 4: Residual4
-- statement:
--   Establish the exact original unconditional polynomial equality recurrence1Residual4 over the rational polynomial ring. All polynomial values are independently kernel compared with the pinned originals. No hypothesis or coefficient is changed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual4. Apache-2.0 attribution preserved. Exact original complete Lean AST signature and resolved references retain every operand. Newly exported values have independent kernel-reflexivity audits, and the original theorem type is independently kernel compared with the copied equality before publication. Logical equivalence of a generic certificate is claimed, not definitional equality; its definition contains no constructed equality proof. Named downstream consumers: unchanged normalized coefficient 4, first recurrence, bounded resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner4_exact_helper_Residual4 :
    MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left4 =
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4 +
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm4 +
      MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4 := by sorry
