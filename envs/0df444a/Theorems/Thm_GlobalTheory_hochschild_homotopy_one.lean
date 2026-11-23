-- Prove2me | Theorems.Thm_GlobalTheory_hochschild_homotopy_one
-- name    : GlobalTheory.hochschild_homotopy_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:28.002029+00:00
-- url     : https://prove2.me/theorems/474b68ce-c2c8-4209-90e4-b66c8bda3483
-- title:
--   Global Theory: hochschild homotopy one
-- statement:
--   The Global Theory construction uses the hochschild homotopy one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L191-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L191-L214

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
variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {X : Type*} [AddMonoid X]

theorem GlobalTheory.hochschild_homotopy_one (ρ : M →ₗ[R] M ⊗[R] R[X]) (f : M ⊗[R] R[X]) :
    (tensorCoeff R R[X] (0 : X)).lTensor M (hochschildD₁ ρ f) -
      hochschildD₀ ρ (tensorCoeff R M 0 f) = f := by sorry
