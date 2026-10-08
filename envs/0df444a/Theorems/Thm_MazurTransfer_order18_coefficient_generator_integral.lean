-- Prove2me | Theorems.Thm_MazurTransfer_order18_coefficient_generator_integral
-- name    : MazurTransfer.order18_coefficient_generator_integral
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T17:30:47.665989+00:00
-- url     : https://prove2.me/theorems/65241b83-df92-4888-9c1c-5718c3d714cc
-- title:
--   Order18: the real cubic coefficient generator is an algebraic integer
-- statement:
--   Let \(K=\mathbb Q[T]/(T^3-3T-1)\) and let \(\tau\in K\) be the image of \(T\). Then \(\tau\) is integral over \(\mathbb Z\). This supplies the integral generator used to construct the actual coefficient-field dyadic prime.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original typed dependencies and whole Lean AST declarations of the monic integral polynomial and its vanishing at the coefficient generator. Original Apache-2.0 header and upstream attribution retained. A separate mathematical certificate supplies the witness to the pure coefficient-integer data, rather than putting an unproved arithmetic existence assertion in a definition package. Named downstream consumer: the coefficient-prime certificate for the unchanged order18 local descent exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order18CoefficientFields

theorem MazurTransfer.order18_coefficient_generator_integral : IsIntegral ℤ MazurTorsion.XOneEighteenRealCubicQuotient.tau := by sorry
