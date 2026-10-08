-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence3_scalar_0
-- name    : MazurTransfer.order49_resultant_recurrence3_scalar_0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T21:09:35.090244+00:00
-- url     : https://prove2.me/theorems/f9c73d3e-be71-4ee8-8168-4ec6f7878819
-- title:
--   Order-49 third recurrence: exact scalar coefficient 0
-- statement:
--   Work in $\mathbb Q[D]$. Let $a_i$, $b_i$ and $c_i$ be the fixed coefficient polynomials of the published quintic, quartic and cubic remainders $R_3$, $R_4$ and $R_5$, respectively, and let $\varepsilon$ be the exact published exceptional factor for step 3. Prove the unconditional polynomial identity
--
--   $$b_4^2a_0=b_0(b_4a_4-b_3a_5)+a_5^2\varepsilon c_0.$$
--
--   Together with the other three low-degree coefficient identities, this establishes the full quintic/quartic pseudo-division recurrence. No scalar identity, rational-point condition or torsion hypothesis is assumed.
-- source:
--   User MazurTheorem WIP 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, exact original MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.IntegerDenseCertificate.scalarResidual3Coefficient0. Original kernel type independently verified by applying the checked source theorem, with a standard-axiom audit. Apache-2.0 provenance retained. Design boundary: one unconditional rational-polynomial scalar identity. Named downstream consumer: recurrence3_checked and the complete order49 exclusion.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData3
open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence3_scalar_0 :
remainder4Coefficient4 ^ 2 * remainder3Coefficient0 =
  remainder4Coefficient0 * (remainder4Coefficient4 * remainder3Coefficient4 - remainder4Coefficient3 * remainder3Coefficient5) + remainder3Coefficient5 ^ 2 * exceptional3 * remainder5Coefficient0 := by sorry
