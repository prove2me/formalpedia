-- Prove2me | Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
-- name    : GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:07.997376+00:00
-- url     : https://prove2.me/theorems/931b963c-c471-423d-9922-afae5ea33c4d
-- title:
--   Global Theory: coe units Add Monoid Algebra Equiv
-- statement:
--   The Global Theory construction uses the coe units Add Monoid Algebra Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L59-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra
open GlobalTheory
variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]
variable [IsDomain A]
variable [Module.Free ℤ X]

theorem GlobalTheory.coe_unitsAddMonoidAlgebraEquiv (p : Aˣ × Multiplicative X) :
    (unitsAddMonoidAlgebraEquiv A X p : A[X]) = single p.2.toAdd (p.1 : A) := by sorry

attribute [defeq] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
