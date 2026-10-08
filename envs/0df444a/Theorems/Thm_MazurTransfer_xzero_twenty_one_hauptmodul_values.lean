-- Prove2me | Theorems.Thm_MazurTransfer_xzero_twenty_one_hauptmodul_values
-- name    : MazurTransfer.xzero_twenty_one_hauptmodul_values
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T11:25:56.761149+00:00
-- url     : https://prove2.me/theorems/64082011-9c58-4e41-8d27-ffd4a1153a7f
-- title:
--   Rational hauptmodul values on X₀(21)
-- statement:
--   Let a and b be nonzero rational numbers satisfying the denominator-cleared fibre-product equation $$ (a+27)(a+3)^3 b^7=a(b^2+13b+49)(b^2+245b+2401)^3. $$ Then a is one of the four values $$-18, -1152, -81/2, -81/128.$$ This is the rational-value classification on the plane model of $X_0(21)$ that supplies the modular-curve input to the order-21 torsion exclusion.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, MazurTorsion/NumberTheory/XZeroTwentyOneTransfer.lean, hauptmodulPair_t₃_cases. All birational-map polynomial certificates are preserved as complete Lean AST declarations. The separate seven-affine-point classification is used through its exact public contract. Original Apache-2.0 source headers retained.

import Mathlib

theorem MazurTransfer.xzero_twenty_one_hauptmodul_values (t₃ t₇ : ℚ) (h3 : t₃ ≠ 0) (h7 : t₇ ≠ 0)
    (hpair : (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 =
      t₃ * (t₇ ^ 2 + 13 * t₇ + 49) * (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3) :
    t₃ = -18 ∨ t₃ = -1152 ∨ t₃ = -81 / 2 ∨ t₃ = -81 / 128 := by sorry
