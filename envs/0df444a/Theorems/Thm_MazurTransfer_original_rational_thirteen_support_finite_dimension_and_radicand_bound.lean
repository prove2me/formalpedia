-- Prove2me | Theorems.Thm_MazurTransfer_original_rational_thirteen_support_finite_dimension_and_radicand_bound
-- name    : MazurTransfer.original_rational_thirteen_support_finite_dimension_and_radicand_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T20:26:34.308947+00:00
-- url     : https://prove2.me/theorems/24a6d751-00a0-4593-96ec-edd3aa415ac1
-- statement:
--   The original rational nineteenth-power classes with zero prime valuation coordinates outside thirteen inject into F19 by their thirteen-coordinate. They therefore form a finite dimensional F19 space of dimension at most one. The original membership criterion and prime divisibility criterion are retained. Any original radicand linear injection with image in that same support space gives the same finite dimension bound. All six complete original propositions and every support, injectivity and module hypothesis are retained. Named downstream consumer: the original selected pi Selmer radicand bound.

import Definitions.Def_MazurTransfer_OriginalRationalThirteenSupportedPowerClassSubmoduleData20261019
import Theorems.Thm_MazurTransfer_original_rational_nineteenth_power_valuation_formula_and_zero_detection
noncomputable section
open MazurTransfer RationalNineteenthPowerClasses RationalNineteenthPowerValuations RationalThirteenPowerClassBound
attribute [local instance] MazurTransfer.RationalThirteenPowerClassBound.instModuleZModOfNatNatAdditivePowerClasses_rationalThirteenPowerClassBound
attribute [local instance] MazurTransfer.RationalThirteenPowerClassBound.instFactPrimeOfNatNat_rationalThirteenPowerClassBound

theorem MazurTransfer.original_rational_thirteen_support_finite_dimension_and_radicand_bound : (∀ (x : Additive PowerClasses), x ∈ thirteenSupport ↔ ∀ (q : ℕ) (hq : q.Prime), q ≠ 13 → valuationLinearMap q hq x = 0) ∧ (Function.Injective thirteenCoordinate) ∧ (FiniteDimensional (ZMod 19) thirteenSupport) ∧ (Module.finrank (ZMod 19) thirteenSupport ≤ 1) ∧ (∀ (a : ℚˣ)
    (hval : ∀ (q : ℕ), q.Prime → q ≠ 13 → (19 : ℤ) ∣ padicValRat q (a : ℚ)), Additive.ofMul (classOf a) ∈ thirteenSupport) ∧ (∀ {W : Type} [AddCommGroup W] [Module (ZMod 19) W] (f : W →ₗ[ZMod 19] Additive PowerClasses) (hi : Function.Injective f)
    (hf : ∀ x : W, f x ∈ thirteenSupport), FiniteDimensional (ZMod 19) W ∧ Module.finrank (ZMod 19) W ≤ 1) := by sorry
