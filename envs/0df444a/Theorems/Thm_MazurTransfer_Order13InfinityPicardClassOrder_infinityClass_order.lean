-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_order
-- name    : MazurTransfer.Order13InfinityPicardClassOrder.infinityClass_order
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T14:44:33.890663+00:00
-- url     : https://prove2.me/theorems/594d419c-01e8-4158-8799-c9975f85a281
-- title:
--   The original actual infinity divisor class has exact additive order nineteen
-- statement:
--   The original arithmetic Picard class of the difference between the two canonical rational infinity places of the literal order-13 curve has exact additive order $$\operatorname{ord}(c)=19.$$ It therefore generates a cyclic subgroup of order nineteen in arithmetic $\operatorname{Pic}^0$, supplying the lower bound to match the proved rational torsion bound.
-- source:
--   Original complete infinityClass_order statement and main proof, with original nineteen_divisor_eq_pellDivisor and nineteen_smul_infinityClass helper proofs, from MazurTheorem Order13InfinityPicardClassOrder.lean, Apache-2.0, Vas and contributors. The unchanged original actual divisor/class constructors are supplied by their published Definition. The actual principal-divisor theorem and the exact original nonzero contract, proved directly by the genus obstruction, are public proved dependencies. The complete original closed type is kernel-compared. Named downstream consumer: the exact lower bound matching the rational arithmetic Picard torsion bound.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit principal divisor makes the nonzero difference
of the actual infinity section classes an element of exact order nineteen.
Named downstream consumer: the lower bound matching the rational arithmetic
Picard torsion bound from the two good reductions.
-/
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellDivisor_isPrincipal
import Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_ne_zero
noncomputable section
open MazurTransfer
open Order13InfinityPicardClassOrder
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13PellPrincipalDivisor Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13InfinityPicardClassOrder.infinityClass_order : addOrderOf infinityClass = 19 := by sorry
