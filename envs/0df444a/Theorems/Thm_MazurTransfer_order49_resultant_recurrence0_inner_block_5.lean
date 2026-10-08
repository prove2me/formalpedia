-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_5
-- name    : MazurTransfer.order49_resultant_recurrence0_inner_block_5
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:12:03.978575+00:00
-- url     : https://prove2.me/theorems/91f0433a-8f25-40a3-8592-e56318331bbb
-- title:
--   Order-49 first recurrence: coefficient block 5
-- statement:
--   Work in $\mathbb Q[T][X]$ with the fixed selection polynomial $R_0$, division polynomial $R_1$, quotient $Q_0$, exceptional factor $\varepsilon_0$ and remainder $R_2$ of the published order-seven branch-zero data. This block asserts every original expanded coefficient identity for indices 30 through 33: the coefficient of $X^j$ in $R_0$ equals the convolution coefficient of $R_1Q_0$ plus that of $\varepsilon_0R_2$. Each equality is an identity of whole polynomials in $T$. Together the six blocks provide all 34 arithmetic coefficients of the first bounded-resultant recurrence; degree bounds separately handle larger indices.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart5.lean; original declarations recurrence0Inner30, recurrence0Inner31, recurrence0Inner32, recurrence0Inner33. Each complete original formal type is selected by Lean-resolved AST signature ranges; all mathematical types and proof values are retained. Source license/header retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence0_inner_block_5 :
(Internal.selectionCofactorCoefficient30 =
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient23) ∧
(Internal.selectionCofactorCoefficient31 =
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient24) ∧
(Internal.selectionCofactorCoefficient32 =
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient25) ∧
(Internal.selectionCofactorCoefficient33 =
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient26) := by sorry
