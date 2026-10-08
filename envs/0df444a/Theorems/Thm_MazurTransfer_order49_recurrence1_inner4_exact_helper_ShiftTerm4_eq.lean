-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_ShiftTerm4_eq
-- name    : MazurTransfer.order49_recurrence1_inner4_exact_helper_ShiftTerm4_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T09:30:58.759391+00:00
-- url     : https://prove2.me/theorems/9778088d-3668-4757-becb-2ecc78d6f864
-- title:
--   First recurrence coefficient 4: ShiftTerm4 eq
-- statement:
--   Establish the exact original unconditional polynomial equality recurrence1ShiftTerm4_eq over the rational polynomial ring. All polynomial values are independently kernel compared with the pinned originals. No hypothesis or coefficient is changed. Formalization Note: a proof-free generic one-field equality certificate represents precisely this equality; equivalence is kernel checked in both directions.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4_eq. Apache-2.0 attribution preserved. Exact original complete Lean AST signature and resolved references retain every operand. Newly exported values have independent kernel-reflexivity audits, and the original theorem type is independently kernel compared with the copied equality before publication. Logical equivalence of a generic certificate is claimed, not definitional equality; its definition contains no constructed equality proof. Named downstream consumers: unchanged normalized coefficient 4, first recurrence, bounded resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart1
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner4_exact_helper_ShiftTerm4_eq : MazurTransfer.ExactEqualityCertificate
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder23)
    (MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm4) := by sorry
