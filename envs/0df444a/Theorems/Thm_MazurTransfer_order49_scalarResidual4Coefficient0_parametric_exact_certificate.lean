-- Prove2me | Theorems.Thm_MazurTransfer_order49_scalarResidual4Coefficient0_parametric_exact_certificate
-- name    : MazurTransfer.order49_scalarResidual4Coefficient0_parametric_exact_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T10:13:25.061012+00:00
-- url     : https://prove2.me/theorems/c46d9488-41d2-46fb-ba00-2ce7113168e0
-- title:
--   Order49 recurrence 4: exact scalar coefficient 0
-- statement:
--   Let $R_{j,\ell}\in\mathbb{Q}[t]$ be the fixed coefficient polynomials of the original order-49 pseudo-division data, and let $E_{4}\in\mathbb{Q}[t]$ be its exceptional factor for recurrence 4. Put
--   \[a=R_{5,3},\qquad b=R_{4,4},\qquad q=aR_{4,3}-R_{5,2}b.\]
--   Prove the unconditional polynomial identity
--   \[a^2 R_{4,0}=R_{5,0}q + b^2 E_{4} R_{6,0}.\]
--   This supplies coefficient 0 in the complete recurrence 4 identity, preserving all original polynomial values. Formalization Note: a proof-free generic one-field equality certificate represents exactly this equality; equivalence is kernel checked in both directions.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.scalarResidual4Coefficient0. Apache-2.0 provenance retained. The complete Lean AST signature and resolved-reference ranges select every original operand. All type dependencies are already published exact original polynomial data with independent kernel-value audits. The original theorem type is independently compared by kernel-reflexivity with the copied equality before publication. No new hypothesis, coefficient or mathematical strengthening occurs. Generic certificate construction and projection are checked in both directions, not claimed to be definitional equality. The contract is Open until an actual proof is accepted. Named downstream consumers: unchanged recurrence 4, bounded-resultant nonvanishing and full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_ExactEqualityCertificate
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData2
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData4
open Polynomial

theorem MazurTransfer.order49_scalarResidual4Coefficient0_parametric_exact_certificate : MazurTransfer.ExactEqualityCertificate (α := Polynomial ℚ)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient0)
    (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient0 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient3 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient3 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 ^ 2 * MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional4 *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder6Coefficient0) := by sorry
