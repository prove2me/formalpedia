-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_valuation_formula_and_zero_detection
-- name    : MazurTransfer.original_rational_nineteenth_power_valuation_formula_and_zero_detection
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T20:18:12.464733+00:00
-- url     : https://prove2.me/theorems/a0e7d825-094b-47cc-8c06-bd30dc3b0305
-- statement:
--   The original valuation coordinate of a rational nineteenth-power class is its rational prime valuation modulo nineteen. If all prime coordinates of a genuine rational power class vanish, the constructive nineteenth-root criterion shows its class is one, or zero in the additive presentation. All three complete original propositions and the same quotient constructors are retained. Named downstream consumer: the rational thirteen-support dimension theorem and selected pi Selmer radicand map.

import Definitions.Def_MazurTransfer_OriginalRationalNineteenthPowerValuationCoordinateData20261019
import Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_class_equality_and_exponent
import Theorems.Thm_MazurTransfer_original_nineteenth_roots_from_natural_integer_rational_prime_valuations
noncomputable section
open MazurTransfer RationalNineteenthPowerClasses RationalNineteenthPowerValuations
attribute [local instance] MazurTransfer.RationalNineteenthPowerValuations.instModuleZModOfNatNatAdditivePowerClasses_rationalNineteenthPowerValuations

theorem MazurTransfer.original_rational_nineteenth_power_valuation_formula_and_zero_detection : (∀ (p : ℕ) (hp : p.Prime) (a : ℚˣ), valuationLinearMap p hp (Additive.ofMul (classOf a)) = ((padicValRat p (a : ℚ) : ℤ) : ZMod 19)) ∧ (∀ (y : PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationClassHom p hp y = 1), y = 1) ∧ (∀ (x : Additive PowerClasses)
    (h : ∀ (p : ℕ) (hp : p.Prime), valuationLinearMap p hp x = 0), x = 0) := by sorry
