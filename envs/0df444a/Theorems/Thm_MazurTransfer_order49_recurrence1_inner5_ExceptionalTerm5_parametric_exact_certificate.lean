-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner5_ExceptionalTerm5_parametric_exact_certificate
-- name    : MazurTransfer.order49_recurrence1_inner5_ExceptionalTerm5_parametric_exact_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T08:00:56.837977+00:00
-- url     : https://prove2.me/theorems/51affb14-cba9-42ab-895c-1c6d579777d4
-- title:
--   First recurrence: exact ExceptionalTerm5 product identity
-- statement:
--   Let $A$, $R_{3,5}$ and $T_{A,5}$ denote the original first-recurrence polynomials specified by the formal statement in the order-49 resultant certificate. Establish the unconditional polynomial identity
--   \[A R_{3,5} = T_{A,5}.\]
--   The polynomial values are identical to those in the pinned original work. This is one of the six arithmetic identities used in the fifth normalized coefficient identity. Formalization Note: a generic one-field equality certificate represents precisely this equality; logical equivalence has been kernel checked in both directions.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5_eq. The earlier raw-target proof timed out after 300 seconds and its actual submission is retained. This changed statement representation uses the published proof-free generic equality certificate, keeping the exact original operands and all original mathematical proof commands. The whole old AST signature is asserted, copied polynomial values and original theorem type have independent kernel-reflexivity audits, and both directions of certificate equivalence have an ordinary kernel check. Logical equivalence is claimed, not definitional equality. No proof is exported through the definition. Apache-2.0 attribution retained. Named downstream consumers: unchanged original arithmetic helper, normalized inner5, first recurrence and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner5_ExceptionalTerm5_parametric_exact_certificate : MazurTransfer.ExactEqualityCertificate
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Exceptional * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder35)
    (MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ExceptionalTerm5) := by sorry
