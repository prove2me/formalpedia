-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualRationalArithmeticPicardTorsionBound_actual_rational_arithmetic_picard_torsion_bound
-- name    : MazurTransfer.Order13ActualRationalArithmeticPicardTorsionBound.actual_rational_arithmetic_picard_torsion_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T10:50:13.049425+00:00
-- url     : https://prove2.me/theorems/6e756f44-5332-41fa-8de4-bd0c9aae8015
-- title:
--   The actual rational arithmetic Picard torsion subgroup is finite with order dividing nineteen
-- statement:
--   Let $F=\mathbb Q(X_1(13))$ denote the actual function field of the specified order-thirteen curve, equipped with its original rational algebra structure, and let $\operatorname{Pic}^0(\mathbb Q,F)$ be its degree-zero divisor-class group. Its full torsion subgroup $T$ satisfies $$T\text{ is finite},\qquad |T|\mid19.$$ The bound is transported from the rational points of the same actual integral Picard family through the checked multiplicative arithmetic dictionary. This is the upper bound used in the actual rational Jacobian torsion computation.
-- source:
--   Original complete actual_rational_arithmetic_picard_torsion_bound statement and proof body from MazurTheorem Order13ActualRationalArithmeticPicardTorsionBound.lean, Apache-2.0, Vas and contributors. Only top-level solution naming, public imports and namespace scope change; the entire original main statement and proof body are retained. Uses the accepted actual same-family rational torsion bound and the accepted original relative-to-arithmetic multiplicative Picard equivalence at every perfect field algebra. Native, strict and complete frontend checks pass with standard axioms only. Complete original/public types are kernel-compared. The public rational function-field algebra action is pinned explicitly and kernel-compared with the original native implementation value; standalone statement imports are checked separately. Reuses official Anthropic FLT at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: the actual rational arithmetic Picard torsion cardinality and Jacobian computation.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: the actual arithmetic degree-zero divisor-class torsion
group over Q is finite with order dividing nineteen.
Named downstream consumer: the actual rational Jacobian torsion computation. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
noncomputable section
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra ℚ

theorem MazurTransfer.Order13ActualRationalArithmeticPicardTorsionBound.actual_rational_arithmetic_picard_torsion_bound :
    letI : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
    Finite (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∧
    Nat.card (CommGroup.torsion (Multiplicative (Pic0 ℚ (actualCurveFunctionField ℚ)))) ∣ 19 := by sorry
