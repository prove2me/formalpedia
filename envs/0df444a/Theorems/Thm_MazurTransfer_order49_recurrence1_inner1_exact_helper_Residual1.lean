-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner1_exact_helper_Residual1
-- name    : MazurTransfer.order49_recurrence1_inner1_exact_helper_Residual1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T09:29:33.310137+00:00
-- url     : https://prove2.me/theorems/54cb268d-adaf-4c9b-baa3-e2754dae6857
-- title:
--   First recurrence coefficient 1: Residual1
-- statement:
--   Establish the exact original unconditional polynomial equality recurrence1Residual1 over the rational polynomial ring. All polynomial values are independently kernel compared with the pinned originals. No hypothesis or coefficient is changed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Residual1. Apache-2.0 attribution preserved. Exact original complete Lean AST signature and resolved references retain every operand. Newly exported values have independent kernel-reflexivity audits, and the original theorem type is independently kernel compared with the copied equality before publication. Logical equivalence of a generic certificate is claimed, not definitional equality; its definition contains no constructed equality proof. Named downstream consumers: unchanged normalized coefficient 1, first recurrence, bounded resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart0
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart2
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner1ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner1_exact_helper_Residual1 :
    MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left1 =
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm1 +
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1QuotientTerm1 +
      MazurTransfer.Order49Recurrence1Inner1ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm1 := by sorry
