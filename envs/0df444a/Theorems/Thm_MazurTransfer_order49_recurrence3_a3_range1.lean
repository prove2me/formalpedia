-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_a3_range1
-- name    : MazurTransfer.order49_recurrence3_a3_range1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T01:12:37.777986+00:00
-- url     : https://prove2.me/theorems/0fd7460f-859b-4c67-9c13-6d0af0fc2480
-- title:
--   Order-49 third recurrence: a3_range1
-- statement:
--   Interpret a little-endian integer coefficient list as a polynomial over the rationals. The exact original interpretation contract a3_range1 holds, with every coefficient and any quantified list argument retained. This connects the audited integer data to the original rational polynomial operations or coefficient table in the third pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 per-file headers and authors retained. Original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseBridge.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a3_range1 selected by kernel dependencies and complete original Lean AST source ranges. Integer model definitions have separately checked original-value equivalences. Original rational coefficient definitions reused unchanged. Proof names and resolved references are namespace-separated at AST-owned byte ranges. No proof-limit increases or new mathematical hypotheses. Named downstream consumers: the four exact original recurrence3 scalar identities and full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Mathlib.Algebra.Polynomial.Degree.Lemmas
open Polynomial

theorem MazurTransfer.order49_recurrence3_a3_range1 (n : ℕ) (hlo : 16 ≤ n) (hhi : n < 32) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a3.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient3.coeff n := by sorry
