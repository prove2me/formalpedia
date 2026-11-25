-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conjTranspose_mem_indefiniteUnitaryLieAlgebra
-- name    : GroundTheory.Automorphic.conjTranspose_mem_indefiniteUnitaryLieAlgebra
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:37.294267+00:00
-- url     : https://prove2.me/theorems/05fe8f7c-a310-405a-a756-d0c6d1f3f193
-- title:
--   Automorphic: conj Transpose mem indefinite Unitary Lie Algebra
-- statement:
--   The Automorphic construction uses the conj Transpose mem indefinite Unitary Lie Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L345-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L345-L352

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.conjTranspose_mem_indefiniteUnitaryLieAlgebra {p q : ℕ}
    {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hX : X ∈ indefiniteUnitaryLieAlgebra p q) :
    Xᴴ ∈ indefiniteUnitaryLieAlgebra p q := by sorry
