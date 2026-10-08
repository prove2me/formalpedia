-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_b4Square
-- name    : MazurTransfer.order49_recurrence3_toPolynomial_b4Square
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T01:30:37.206605+00:00
-- url     : https://prove2.me/theorems/f3cd66e7-cf43-4702-95de-95fdc3d8e7bf
-- title:
--   Order-49 third recurrence: toPolynomial_b4Square
-- statement:
--   Interpret a little-endian integer coefficient list as a polynomial over the rationals. The exact original interpretation contract toPolynomial_b4Square holds, with every coefficient and any quantified list argument retained. This connects the audited integer data to the original rational polynomial operations or coefficient table in the third pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 per-file headers and authors retained. Original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial_b4Square selected by kernel dependencies and complete original Lean AST source ranges. Integer model definitions have separately checked original-value equivalences. Original rational coefficient definitions reused unchanged. Proof names and resolved references are namespace-separated at AST-owned byte ranges. No proof-limit increases or new mathematical hypotheses. Named downstream consumers: the four exact original recurrence3 scalar identities and full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData2
open Polynomial

theorem MazurTransfer.order49_recurrence3_toPolynomial_b4Square :
    MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.b4Square = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder4Coefficient4 ^ 2 := by sorry
