-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_left5_parametric_exact_certificate
-- name    : MazurTransfer.order49_recurrence1_left5_parametric_exact_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T07:54:52.346065+00:00
-- url     : https://prove2.me/theorems/d9d39b96-8095-4ebc-ba48-974c17298f12
-- title:
--   First recurrence: exact left product identity
-- statement:
--   Let $S_5$, $B_6^{(2)}$ and $L_5$ be the original first-recurrence source, square and left-hand polynomials in the order-49 resultant certificate. Establish the unconditional polynomial identity
--   \[S_5 B_6^{(2)} = L_5.\]
--   The polynomial values are identical to those in the pinned original work. This equality is one of the six arithmetic identities used to prove the fifth normalized coefficient identity. Formalization Note: the target uses a generic one-field equality certificate; its logical equivalence to the exact original equality has been kernel checked in both directions.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5_eq. The earlier raw equality publication timed out after 300 seconds; its job is retained. This new statement uses the published proof-free generic equality certificate and retains precisely the original operands and hypotheses. The exact old AST signature is asserted, the copied helper values and original theorem type have independent kernel-reflexivity audits, and both directions of certificate equivalence have an ordinary kernel check. Logical equivalence is claimed, not definitional equality. No proof is exported through the definition. Apache-2.0 attribution retained. Named downstream consumers: normalized inner5 identity, first recurrence and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49Recurrence1Inner5ExactHelperData
import Definitions.Def_MazurTransfer_Order49Recurrence1NormalizedData
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial

theorem MazurTransfer.order49_recurrence1_left5_parametric_exact_certificate : MazurTransfer.ExactEqualityCertificate
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Source5 * MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1B6Square)
    (MazurTransfer.Order49Recurrence1Inner5ExactHelperData.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1Left5) := by sorry
