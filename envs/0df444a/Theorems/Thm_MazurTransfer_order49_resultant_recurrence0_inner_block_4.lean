-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_4
-- name    : MazurTransfer.order49_resultant_recurrence0_inner_block_4
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:08:18.697242+00:00
-- url     : https://prove2.me/theorems/a9d54dde-e4ac-43ca-b52f-c898e8612aa2
-- title:
--   Order-49 first recurrence: coefficient block 4
-- statement:
--   Work in $\mathbb Q[T][X]$ with the fixed selection polynomial $R_0$, division polynomial $R_1$, quotient $Q_0$, exceptional factor $\varepsilon_0$ and remainder $R_2$ of the published order-seven branch-zero data. This block asserts every original expanded coefficient identity for indices 24 through 29: the coefficient of $X^j$ in $R_0$ equals the convolution coefficient of $R_1Q_0$ plus that of $\varepsilon_0R_2$. Each equality is an identity of whole polynomials in $T$. Together the six blocks provide all 34 arithmetic coefficients of the first bounded-resultant recurrence; degree bounds separately handle larger indices.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart4.lean; original declarations recurrence0Inner24, recurrence0Inner25, recurrence0Inner26, recurrence0Inner27, recurrence0Inner28, recurrence0Inner29. Each complete original formal type is selected by Lean-resolved AST signature ranges; all mathematical types and proof values are retained. Source license/header retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence0_inner_block_4 :
(Internal.selectionCofactorCoefficient24 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient17) ∧
(Internal.selectionCofactorCoefficient25 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient18) ∧
(Internal.selectionCofactorCoefficient26 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient19) ∧
(Internal.selectionCofactorCoefficient27 =
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient20) ∧
(Internal.selectionCofactorCoefficient28 =
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient21) ∧
(Internal.selectionCofactorCoefficient29 =
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient22) := by sorry
