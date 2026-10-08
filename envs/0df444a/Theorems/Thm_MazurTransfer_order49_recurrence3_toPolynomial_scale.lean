-- Prove2me | Theorems.Thm_MazurTransfer_order49_recurrence3_toPolynomial_scale
-- name    : MazurTransfer.order49_recurrence3_toPolynomial_scale
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T23:04:20.934343+00:00
-- url     : https://prove2.me/theorems/fe664bae-ddc4-466f-8bff-5bc274696f5b
-- title:
--   Order-49 third recurrence: toPolynomial_scale
-- statement:
--   Interpret a little-endian integer coefficient list as a polynomial over the rationals. The exact original interpretation contract toPolynomial_scale holds, with every coefficient and any quantified list argument retained. This connects the audited integer data to the original rational polynomial operations or coefficient table in the third pseudo-division recurrence.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 per-file headers and authors retained. Original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial_scale selected by kernel dependencies and complete original Lean AST source ranges. Integer model definitions have separately checked original-value equivalences. Original rational coefficient definitions reused unchanged. Proof names and resolved references are namespace-separated at AST-owned byte ranges. No proof-limit increases or new mathematical hypotheses. Named downstream consumers: the four exact original recurrence3 scalar identities and full order49 exclusion.

import Definitions.Def_MazurTransfer_Order49Recurrence3IntegerArithmetic
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData0
import Definitions.Def_MazurTransfer_Order49Recurrence3StandaloneDenseData3
open Polynomial

theorem MazurTransfer.order49_recurrence3_toPolynomial_scale (a : ℤ) (xs : List ℤ) :
    MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial (MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scale a xs) = C (a : ℚ) * MazurTransfer.Order49Recurrence3Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.toPolynomial xs := by sorry
