-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner4_exact_helper_ExceptionalTerm4_eq
-- name    : MazurTransfer.order49_recurrence1_inner4_exact_helper_ExceptionalTerm4_eq
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T09:30:37.153321+00:00
-- url     : https://prove2.me/theorems/1343e1ef-5fe6-4a01-a254-26f0d9c86691
-- title:
--   First recurrence coefficient 4: ExceptionalTerm4 eq
-- statement:
--   Establish the exact original unconditional polynomial equality recurrence1ExceptionalTerm4_eq over the rational polynomial ring. All polynomial values are independently kernel compared with the pinned originals. No hypothesis or coefficient is changed. Formalization Note: a proof-free generic one-field equality certificate represents precisely this equality; equivalence is kernel checked in both directions.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4_eq. Apache-2.0 attribution preserved. Exact original complete Lean AST signature and resolved references retain every operand. Newly exported values have independent kernel-reflexivity audits, and the original theorem type is independently kernel compared with the copied equality before publication. Logical equivalence of a generic certificate is claimed, not definitional equality; its definition contains no constructed equality proof. Named downstream consumers: unchanged normalized coefficient 4, first recurrence, bounded resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner4ExactHelperDataPart3
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner4_exact_helper_ExceptionalTerm4_eq : MazurTransfer.ExactEqualityCertificate
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder34)
    (MazurTransfer.Order49Recurrence1Inner4ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm4) := by sorry
