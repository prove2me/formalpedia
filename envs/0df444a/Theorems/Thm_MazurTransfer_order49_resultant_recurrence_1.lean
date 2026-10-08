-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence_1
-- name    : MazurTransfer.order49_resultant_recurrence_1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:08:37.678675+00:00
-- url     : https://prove2.me/theorems/5cf76058-5014-4214-bf8c-3cc0667004a1
-- title:
--   Order-49 bounded-resultant arithmetic recurrence 1
-- statement:
--   Work in the bivariate polynomial ring $\mathbb Q[T][X]$. Let $R_i$, $Q_i$ and $\varepsilon_i$ denote the fixed remainders, quotient polynomials and exceptional factors in the separately published order-seven branch-zero data. For $1\leq i\leq7$, let $a_i=[X^{8-i}]R_i$. Then the exact recurrence at step 1 is
--
--   $$
--   a_{2}^2R_{1}=R_{2}Q_{1}+a_{1}^2\varepsilon_{1}R_{3}.
--   $$
--
--   This is an unconditional equality of the fixed full polynomials, including all coefficients. It is one of seven arithmetic identities used to telescope the bounded resultant certificate for the order-49 exclusion. It makes no rational-point or torsion assumption.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1_checked in MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1.lean, declaration range 173-263. The complete original source is checked in the exact order49 tower. The formal target is exactly its original recurrence Prop, whose mathematical definition is preserved byte-for-byte in the public data files. Apache-2.0 provenance retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.generic_resultant_eq_resultantFactorData.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData6

theorem MazurTransfer.order49_resultant_recurrence_1 :
MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence1 := by sorry
