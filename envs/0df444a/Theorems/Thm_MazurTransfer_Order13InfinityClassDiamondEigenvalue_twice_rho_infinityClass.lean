-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityClassDiamondEigenvalue_twice_rho_infinityClass
-- name    : MazurTransfer.Order13InfinityClassDiamondEigenvalue.twice_rho_infinityClass
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:48:50.127491+00:00
-- url     : https://prove2.me/theorems/93e17d50-8793-4834-8112-b28badb1c520
-- title:
--   The infinity class has diamond eigenvalue five halves
-- statement:
--   For the original rational infinity difference class A and field-parametric Picard diamond rho, twice rho(A) equals five times A. The proof uses the cubic cusp principal-divisor relation and the accepted rational quadratic diamond relation.
-- source:
--   MazurTheorem Order13InfinityClassDiamondEigenvalue.twice_rho_infinityClass, exact original closed proposition; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder Order13FieldDiamondPicardEndomorphisms
local instance publicInfinityClassEigenvalueFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicInfinityClassEigenvalueAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13InfinityClassDiamondEigenvalue.twice_rho_infinityClass : (2 : ℤ) • (rho ℚ) infinityClass = (5 : ℤ) • infinityClass := by sorry
