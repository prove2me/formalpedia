-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_piConjugate_infinityClass
-- name    : MazurTransfer.Order13InfinityClassActualNormKernels.actual_piConjugate_infinityClass
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:54:47.785713+00:00
-- url     : https://prove2.me/theorems/390d0adb-d261-4c74-8f82-bc87b426ddc0
-- title:
--   The conjugate norm kills the infinity class
-- statement:
--   The original rational infinity class is annihilated by the actual conjugate norm.
-- source:
--   MazurTheorem Order13InfinityClassActualNormKernels.actual_piConjugate_infinityClass; exact complete original proposition retained; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
noncomputable section
open MazurTransfer AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder Order13ActualDiamondPicardEndomorphisms
local instance publicActualConjugateInfinityOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance publicActualConjugateInfinityOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13InfinityClassActualNormKernels.actual_piConjugate_infinityClass  : Order13ActualDiamondPicardEndomorphisms.piConjugate infinityClass = 0 := by sorry
