-- Prove2me | Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_3
-- name    : MazurTransfer.order49_resultant_recurrence0_inner_block_3
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T19:12:08.017282+00:00
-- url     : https://prove2.me/theorems/928cb7f4-5497-4109-b444-3c507ee05747
-- title:
--   Order-49 first recurrence: coefficient block 3
-- statement:
--   Work in $\mathbb Q[T][X]$ with the fixed selection polynomial $R_0$, division polynomial $R_1$, quotient $Q_0$, exceptional factor $\varepsilon_0$ and remainder $R_2$ of the published order-seven branch-zero data. This block asserts every original expanded coefficient identity for indices 18 through 23: the coefficient of $X^j$ in $R_0$ equals the convolution coefficient of $R_1Q_0$ plus that of $\varepsilon_0R_2$. Each equality is an identity of whole polynomials in $T$. Together the six blocks provide all 34 arithmetic coefficients of the first bounded-resultant recurrence; degree bounds separately handle larger indices.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart3.lean; original declarations recurrence0Inner18, recurrence0Inner19, recurrence0Inner20, recurrence0Inner21, recurrence0Inner22, recurrence0Inner23. Each complete original formal type is selected by Lean-resolved AST signature ranges; all mathematical types and proof values are retained. Source license/header retained. Named downstream consumer: MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked.

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
open Polynomial MazurTorsion.Kubert.OrderSevenBacktrackingCertificate MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem MazurTransfer.order49_resultant_recurrence0_inner_block_3 :
(Internal.selectionCofactorCoefficient18 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient11) ∧
(Internal.selectionCofactorCoefficient19 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient12) ∧
(Internal.selectionCofactorCoefficient20 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient13) ∧
(Internal.selectionCofactorCoefficient21 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient14) ∧
(Internal.selectionCofactorCoefficient22 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient15) ∧
(Internal.selectionCofactorCoefficient23 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient16) := by sorry
