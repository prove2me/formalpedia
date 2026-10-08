-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_c0_range8
-- name    : MazurTransfer.order49_recurrence3_c0_range8
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T01:08:25.489993+00:00
-- url     : https://prove2.me/theorems/5acf5324-2623-4fa9-997e-7709d463cc6c
-- title:
--   Order-49 third recurrence: c0_range8
-- statement:
--   Interpret a little-endian integer coefficient list as a polynomial over the rationals. The exact original interpretation contract c0_range8 holds, with every coefficient and any quantified list argument retained. This connects the audited integer data to the original rational polynomial operations or coefficient table in the third pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 per-file headers and authors retained. Original _private.MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseBridge.0.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.c0_range8 selected by kernel dependencies and complete original Lean AST source ranges. Integer model definitions have separately checked original-value equivalences. Original rational coefficient definitions reused unchanged. Proof names and resolved references are namespace-separated at AST-owned byte ranges. No proof-limit increases or new mathematical hypotheses. Named downstream consumers: the four exact original recurrence3 scalar identities and full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerTables
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData3
import Mathlib.Algebra.Polynomial.Degree.Lemmas
open Polynomial

theorem MazurTransfer.order49_recurrence3_c0_range8 (n : ℕ) (hlo : 128 ≤ n) (hhi : n < 144) :
    ((MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.Data.c0.getD n 0 : ℤ) : ℚ) = MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder5Coefficient0.coeff n := by sorry
