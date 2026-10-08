-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence1_inner_3
-- name    : MazurTransfer.order49_recurrence1_inner_3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T01:11:23.056+00:00
-- url     : https://prove2.me/theorems/a6fd9436-1427-4324-80a5-85459497174e
-- title:
--   First order-seven recurrence: recurrence1 inner 3
-- statement:
--   Work in $\mathbb Q[T][X]$. Let $R_i,Q_i,\varepsilon_i$ be the fixed full polynomials of the first order-seven pseudo-division step, and let $a_i=[X^{8-i}]R_i$. This is one of the six original low-degree coefficient identities in $$a_2^2R_1=R_2Q_1+a_1^2\varepsilon_1R_3.$$ All coefficient polynomials and the exceptional factor are the exact independently published data. The identity is unconditional and supplies the complete first recurrence by coefficient comparison.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; Apache-2.0 headers and attribution preserved. Exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_inner_3 in MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Inner. Original kernel dependency from recurrence1_checked and complete Lean AST signature ranges determine this interface. No coefficient, hypothesis, or theorem statement is changed. Named consumers: recurrence1_checked, generic_resultant_eq_resultantFactorData and the full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
open Polynomial

theorem MazurTransfer.order49_recurrence1_inner_3 :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 ^ 2 *
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient3 =
      MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient2 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient3 *
          (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient6 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6 -
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder2Coefficient5 *
              MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7) +
        (MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7 ^ 2 *
            MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.exceptional1) *
          MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3 := by sorry
