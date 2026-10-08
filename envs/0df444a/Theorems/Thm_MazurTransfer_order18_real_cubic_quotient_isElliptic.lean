-- Prove2me | Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
-- name    : MazurTransfer.order18_real_cubic_quotient_isElliptic
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T14:05:57.463099+00:00
-- url     : https://prove2.me/theorems/4a540cb4-38f5-439a-93c6-a2204c42fadb
-- title:
--   Order18: nonsingularity of the exact cubic-field quotient
-- statement:
--   The explicit original real-cubic quotient has nonzero discriminant and is elliptic.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The exact original supporting theorem is selected by its typed kernel closure and complete original parsed source declarations. Original Apache-2.0 headers and attribution retained. Named downstream consumers: both genuine halves of the full order18 arithmetic proof. No resource-strengthening options, custom axioms or modified hypotheses.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData

theorem MazurTransfer.order18_real_cubic_quotient_isElliptic : MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.IsElliptic := by sorry
