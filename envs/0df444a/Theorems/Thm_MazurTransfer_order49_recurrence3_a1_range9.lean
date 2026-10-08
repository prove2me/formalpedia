-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_a1_range9
-- name    : MazurTransfer.order49_recurrence3_a1_range9
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T00:51:21.453086+00:00
-- url     : https://prove2.me/theorems/84a9f188-5225-466d-821b-1a8acdf01266
-- title:
--   Order-49 third recurrence: a1_range9
-- statement:
--   Interpret a little-endian integer coefficient list as a polynomial over the rationals. The exact original interpretation contract a1_range9 holds, with every coefficient and any quantified list argument retained. This connects the audited integer data to the original rational polynomial operations or coefficient table in the third pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 per-file headers and authors retained. Original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseBridge.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a1_range9 selected by kernel dependencies and complete original Lean AST source ranges. Integer model definitions have separately checked original-value equivalences. Original rational coefficient definitions reused unchanged. Proof names and resolved references are namespace-separated at AST-owned byte ranges. No proof-limit increases or new mathematical hypotheses. Named downstream consumers: the four exact original recurrence3 scalar identities and full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Mathlib.Algebra.Polynomial.Degree.Lemmas
open Polynomial

theorem MazurTransfer.order49_recurrence3_a1_range9 (n : ℕ) (hlo : 144 ≤ n) (hhi : n < 151) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a1.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient1.coeff n := by sorry
