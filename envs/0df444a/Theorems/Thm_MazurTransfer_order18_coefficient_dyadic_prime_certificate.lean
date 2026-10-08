-- Prove2me | Theorems.Thm_MazurTransfer_order18_coefficient_dyadic_prime_certificate
-- name    : MazurTransfer.order18_coefficient_dyadic_prime_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T17:36:55.433477+00:00
-- url     : https://prove2.me/theorems/f1f68117-06fb-49b3-8b2d-3a722aa0bd50
-- title:
--   Order18: the coefficient generator satisfies the exact Kummer–Dedekind conditions at two
-- statement:
--   Let \(K=\mathbb Q[T]/(T^3-3T-1)\) and let \(\tau\in\mathcal O_K\) be the published integral coefficient generator. The Kummer–Dedekind exponent attached to \(\tau\) is not divisible by \(2\), and the reduction of \(T^3-3T-1\) modulo \(2\) is one of the monic irreducible factors of the reduced minimal polynomial. These are the two exact arithmetic prerequisites for constructing the original coefficient-field dyadic prime.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, original private coefficient_not_dvd_exponent_two and coefficientPolynomialInt_mem_monicFactors_two closures, selected from typed kernel dependencies and complete Lean AST declarations. Original Apache-2.0 headers and attribution retained. This is an arithmetic certificate separate from the pure integer and completion definition packages. Named downstream consumer: original coefficientPrimeTwoIdeal and coefficientPrimeTwo constructors, then the unchanged order18 local exclusion. No final campaign hypotheses or arithmetic fields are changed.

import Mathlib
import Definitions.Def_MazurTransfer_Order18CoefficientIntegerData

theorem MazurTransfer.order18_coefficient_dyadic_prime_certificate :
    ¬ 2 ∣ _root_.RingOfIntegers.exponent MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientInteger ∧
      MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)) ∈
        _root_.RingOfIntegers.monicFactorsMod MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientInteger 2 := by sorry
