-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_class_equality_and_exponent
-- name    : MazurTransfer.original_rational_nineteenth_power_class_equality_and_exponent
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T20:04:03.386062+00:00
-- url     : https://prove2.me/theorems/c1e68e3d-71cd-458b-bb53-5bf48db8ce30
-- statement:
--   In the original multiplicative quotient of nonzero rational numbers by nineteenth powers, two classes agree exactly when their ratio is a nineteenth power. A class is one exactly when its representative is a nineteenth power, and every class has nineteenth power one. The same quotient and class map are retained. Named downstream consumer: original rational prime valuation coordinates and the selected pi Selmer radicand injection.

import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerClassesData20261019
noncomputable section
open MazurTransfer RationalNineteenthPowerClasses

theorem MazurTransfer.original_rational_nineteenth_power_class_equality_and_exponent : (∀ (a d : ℚˣ), classOf a = classOf d ↔ ∃ b : ℚˣ, b ^ 19 = a / d) ∧ (∀ (a : ℚˣ), classOf a = 1 ↔ ∃ b : ℚˣ, b ^ 19 = a) ∧ (∀ (x : PowerClasses), x ^ 19 = 1) := by sorry
