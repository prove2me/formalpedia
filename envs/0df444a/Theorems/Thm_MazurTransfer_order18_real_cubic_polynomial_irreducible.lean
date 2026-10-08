-- Prove2me | Theorems.Thm_MazurTransfer_order18_real_cubic_polynomial_irreducible
-- name    : MazurTransfer.order18_real_cubic_polynomial_irreducible
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T14:02:11.607133+00:00
-- url     : https://prove2.me/theorems/0e64db61-dd2e-438e-9acb-a93780d49926
-- title:
--   Order18: irreducibility of the exact cubic coefficient polynomial
-- statement:
--   The polynomial T³−3T−1 is irreducible over ℚ.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The exact original supporting theorem is selected by its typed kernel closure and complete original parsed source declarations. Original Apache-2.0 headers and attribution retained. Named downstream consumers: both genuine halves of the full order18 arithmetic proof. No resource-strengthening options, custom axioms or modified hypotheses.

import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicPolynomialData

theorem MazurTransfer.order18_real_cubic_polynomial_irreducible : Irreducible MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial := by sorry
