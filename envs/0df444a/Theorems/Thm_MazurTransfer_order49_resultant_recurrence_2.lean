-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence_2
-- name    : MazurTransfer.order49_resultant_recurrence_2
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:32:35.911021+00:00
-- url     : https://prove2.me/theorems/b17cf8e4-0a49-4d35-acc7-e1e0a097ab69
-- title:
--   Order-49 bounded-resultant arithmetic recurrence 2
-- statement:
--   Work in the bivariate polynomial ring $\mathbb Q[T][X]$. Let $R_i$, $Q_i$ and $\varepsilon_i$ denote the fixed remainders, quotient polynomials and exceptional factors in the separately published order-seven branch-zero data. For $1\leq i\leq7$, let $a_i=[X^{8-i}]R_i$. Then the exact recurrence at step 2 is
--
--   $$
--   a_{3}^2R_{2}=R_{3}Q_{2}+a_{2}^2\varepsilon_{2}R_{4}.
--   $$
--
--   This is an unconditional equality of the fixed full polynomials, including all coefficients. It is one of seven arithmetic identities used to telescope the bounded resultant certificate for the order-49 exclusion. It makes no rational-point or torsion assumption.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2_checked in MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2Lookup.lean, declaration range 193-215. The complete original source is checked in the exact order49 tower. The formal target is exactly its original recurrence Prop, whose mathematical definition is preserved byte-for-byte in the public data files. Apache-2.0 provenance retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.generic_resultant_eq_resultantFactorData. Publication dependency repair: the exact recurrence requires only its original data shard 2 and its predecessors, rather than the unused later recurrence data through step6. The formal theorem bytes are unchanged.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData2

theorem MazurTransfer.order49_resultant_recurrence_2 :
MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence2 := by sorry
