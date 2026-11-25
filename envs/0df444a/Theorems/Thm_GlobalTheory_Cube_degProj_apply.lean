-- Prove2me | Theorems.Thm_GlobalTheory_Cube_degProj_apply
-- name    : GlobalTheory.Cube.degProj_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:44:29.335118+00:00
-- url     : https://prove2.me/theorems/1e8e8339-b3c8-5b66-9737-75efe03c22bc
-- title:
--   Cube: deg Proj apply
-- statement:
--   The Cube construction uses the deg Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L49-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]

theorem GlobalTheory.Cube.degProj_apply (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) (s : Finset ι) :
    degProj A p x s = if s.card = p then x s else 0 := by sorry
