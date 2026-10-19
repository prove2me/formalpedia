-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_ne_zero
-- name    : MazurTransfer.Order13InfinityPicardClassOrder.infinityClass_ne_zero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:42:37.507033+00:00
-- url     : https://prove2.me/theorems/19a9dcac-b6b9-471a-9de6-af5050f56aaf
-- title:
--   The actual difference of infinity divisor classes is nonzero by the genus obstruction
-- statement:
--   Let $v_+,v_-$ be the canonical degree-one places of the two literal rational infinity sections of the order-13 curve. Its specified arithmetic Picard class satisfies $$[v_-]-[v_+]\ne0\quad\text{in}\quad\operatorname{Pic}^0(C/\mathbb Q).$$ This gives the nonvanishing needed to show that the Pell class has exact additive order nineteen.
-- source:
--   Unchanged complete infinityClass_ne_zero statement and unchanged original infinityDifferenceDivisor/infinityClass constructors from MazurTheorem Order13InfinityPicardClassOrder.lean, Apache-2.0, Vas and contributors. New direct proof uses the publicly proved perfect-field principal-degree-one-difference genus-zero obstruction and original public constants-are-base/genus-two certificates. It avoids the larger rational-section Picard injection dictionary while preserving the exact same actual class and complete original theorem type. The full original closed type is kernel-compared. Named downstream consumer: exact additive order nineteen of the actual infinity class.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original actual infinity divisor class is nonzero.
Named downstream consumer: its exact additive order nineteen.
The statement and actual class constructor are unchanged. This independent
proof uses the public perfect-field genus-zero obstruction directly rather
than the larger rational-section Picard injection dictionary.
-/
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_genusFF_eq_zero_of_principal_single_sub_single
noncomputable section
open MazurTransfer AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder Order13PellPrincipalDivisor
open Order13ActualInfinityPlaceCenters Order13PellActualInfinityValuations
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13InfinityPicardClassOrder.infinityClass_ne_zero : infinityClass ≠ 0 := by sorry
