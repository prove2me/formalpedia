-- Prove2me | Theorems.Thm_GlobalTheory_addMonoidAlgebra_coboundary_eq_iff
-- name    : GlobalTheory.addMonoidAlgebra_coboundary_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:56.166491+00:00
-- url     : https://prove2.me/theorems/1ebd92cf-6ee7-4d10-b931-626323dcfb2f
-- title:
--   Global Theory: add Monoid Algebra coboundary eq iff
-- statement:
--   The Global Theory construction uses the add Monoid Algebra coboundary eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsUnitAddMonoidAlgebraIffOfTwoUniqueSums.lean#L127-L136

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
variable {X : Type*} [Zero X] {A : Type*} [Ring A]

theorem GlobalTheory.addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by sorry
