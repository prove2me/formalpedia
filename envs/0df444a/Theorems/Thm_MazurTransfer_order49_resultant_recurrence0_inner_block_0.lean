-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_0
-- name    : MazurTransfer.order49_resultant_recurrence0_inner_block_0
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:09:50.089982+00:00
-- url     : https://prove2.me/theorems/a6409d84-3982-4f04-8abc-cc1097d3efd7
-- title:
--   Order-49 first recurrence: coefficient block 0
-- statement:
--   Work in $\mathbb Q[T][X]$ with the fixed selection polynomial $R_0$, division polynomial $R_1$, quotient $Q_0$, exceptional factor $\varepsilon_0$ and remainder $R_2$ of the published order-seven branch-zero data. This block asserts every original expanded coefficient identity for indices 0 through 5: the coefficient of $X^j$ in $R_0$ equals the convolution coefficient of $R_1Q_0$ plus that of $\varepsilon_0R_2$. Each equality is an identity of whole polynomials in $T$. Together the six blocks provide all 34 arithmetic coefficients of the first bounded-resultant recurrence; degree bounds separately handle larger indices.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart0.lean; original declarations recurrence0Inner0, recurrence0Inner1, recurrence0Inner2, recurrence0Inner3, recurrence0Inner4, recurrence0Inner5. Each complete original formal type is selected by Lean-resolved AST signature ranges; all mathematical types and proof values are retained. Source license/header retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence0_inner_block_0 :
(Internal.selectionCofactorCoefficient0 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient0) ∧
(Internal.selectionCofactorCoefficient1 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient1) ∧
(Internal.selectionCofactorCoefficient2 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient2) ∧
(Internal.selectionCofactorCoefficient3 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient3) ∧
(Internal.selectionCofactorCoefficient4 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient4) ∧
(Internal.selectionCofactorCoefficient5 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient5) := by sorry
