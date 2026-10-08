-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_1
-- name    : MazurTransfer.order49_resultant_recurrence0_inner_block_1
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:10:19.983243+00:00
-- url     : https://prove2.me/theorems/c42da8fb-8bd2-4518-a695-121a001c5796
-- title:
--   Order-49 first recurrence: coefficient block 1
-- statement:
--   Work in $\mathbb Q[T][X]$ with the fixed selection polynomial $R_0$, division polynomial $R_1$, quotient $Q_0$, exceptional factor $\varepsilon_0$ and remainder $R_2$ of the published order-seven branch-zero data. This block asserts every original expanded coefficient identity for indices 6 through 11: the coefficient of $X^j$ in $R_0$ equals the convolution coefficient of $R_1Q_0$ plus that of $\varepsilon_0R_2$. Each equality is an identity of whole polynomials in $T$. Together the six blocks provide all 34 arithmetic coefficients of the first bounded-resultant recurrence; degree bounds separately handle larger indices.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart1.lean; original declarations recurrence0Inner6, recurrence0Inner7, recurrence0Inner8, recurrence0Inner9, recurrence0Inner10, recurrence0Inner11. Each complete original formal type is selected by Lean-resolved AST signature ranges; all mathematical types and proof values are retained. Source license/header retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence0_inner_block_1 :
(Internal.selectionCofactorCoefficient6 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient6) ∧
(Internal.selectionCofactorCoefficient7 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient0) ∧
(Internal.selectionCofactorCoefficient8 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient1) ∧
(Internal.selectionCofactorCoefficient9 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient2) ∧
(Internal.selectionCofactorCoefficient10 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient3) ∧
(Internal.selectionCofactorCoefficient11 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient4) := by sorry
