-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_a4_range2
-- name    : MazurTransfer.order49_recurrence3_a4_range2
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T01:00:11.747185+00:00
-- url     : https://prove2.me/theorems/83342534-c0b3-4fa6-9fc0-ef0bb241c5a6
-- title:
--   Order-49 third recurrence: a4_range2
-- statement:
--   Interpret a little-endian integer coefficient list as a polynomial over the rationals. The exact original interpretation contract a4_range2 holds, with every coefficient and any quantified list argument retained. This connects the audited integer data to the original rational polynomial operations or coefficient table in the third pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 per-file headers and authors retained. Original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseBridge.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.a4_range2 selected by kernel dependencies and complete original Lean AST source ranges. Integer model definitions have separately checked original-value equivalences. Original rational coefficient definitions reused unchanged. Proof names and resolved references are namespace-separated at AST-owned byte ranges. No proof-limit increases or new mathematical hypotheses. Named downstream consumers: the four exact original recurrence3 scalar identities and full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence3ExtraIntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData1
import Mathlib.Algebra.Polynomial.Degree.Lemmas
open Polynomial

theorem MazurTransfer.order49_recurrence3_a4_range2 (n : ℕ) (hlo : 32 ≤ n) (hhi : n < 48) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.a4.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder3Coefficient4.coeff n := by sorry
