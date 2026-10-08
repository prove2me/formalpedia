-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_coefficients
-- name    : MazurTransfer.order27_aggregate_coefficients
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:56.230488+00:00
-- url     : https://prove2.me/theorems/8d7dc1a4-f738-4baf-aec3-c9d0b55fdcf6
-- title:
--   Order-27 third-leg aggregation: coefficients
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zl_brC0, zl_brC1, zl_brC2, zl_brC3 identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_coefficients :
(∀ (f : ℚ),
zlCZero0 f =
      (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9)) ∧
(∀ (f : ℚ),
zlCOne0 f =
      (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 *
        (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3)) ∧
(∀ (f : ℚ),
zlCTwo0 f =
      (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^
        3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2)) ∧
(∀ (f : ℚ),
zlCThree0 f =
      ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3))) := by sorry
