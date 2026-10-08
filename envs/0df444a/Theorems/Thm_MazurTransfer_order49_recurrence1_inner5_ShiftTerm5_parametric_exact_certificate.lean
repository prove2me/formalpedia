-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner5_ShiftTerm5_parametric_exact_certificate
-- name    : MazurTransfer.order49_recurrence1_inner5_ShiftTerm5_parametric_exact_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T07:58:55.33701+00:00
-- url     : https://prove2.me/theorems/3a0ab3ae-68af-424c-b189-1898c6a96521
-- title:
--   First recurrence: exact ShiftTerm5 product identity
-- statement:
--   Let $R_{2,6}$, $R_{2,4}$ and $T_{S,5}$ denote the original first-recurrence polynomials specified by the formal statement in the order-49 resultant certificate. Establish the unconditional polynomial identity
--   \[R_{2,6} R_{2,4} = T_{S,5}.\]
--   The polynomial values are identical to those in the pinned original work. This is one of the six arithmetic identities used in the fifth normalized coefficient identity. Formalization Note: a generic one-field equality certificate represents precisely this equality; logical equivalence has been kernel checked in both directions.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5_eq. The earlier raw-target proof timed out after 300 seconds and its actual submission is retained. This changed statement representation uses the published proof-free generic equality certificate, keeping the exact original operands and all original mathematical proof commands. The whole old AST signature is asserted, copied polynomial values and original theorem type have independent kernel-reflexivity audits, and both directions of certificate equivalence have an ordinary kernel check. Logical equivalence is claimed, not definitional equality. No proof is exported through the definition. Apache-2.0 attribution retained. Named downstream consumers: unchanged original arithmetic helper, normalized inner5, first recurrence and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner5_ShiftTerm5_parametric_exact_certificate : MazurTransfer.ExactEqualityCertificate
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder26 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Remainder24)
    (MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1ShiftTerm5) := by sorry
