-- Prove2me | Theorems.Thm_GlobalTheory_Cube_degSign_apply
-- name    : GlobalTheory.Cube.degSign_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:09.181915+00:00
-- url     : https://prove2.me/theorems/298eadb7-a9d2-41e4-af54-19e9a4a952a9
-- title:
--   Cube: deg Sign apply
-- statement:
--   The Cube construction uses the deg Sign apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L58-L59

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

theorem GlobalTheory.Cube.degSign_apply (A : Cube.{v} ι R) (x : ∀ s, A.obj s) (s : Finset ι) :
    degSign A x s = (-1 : ℤ) ^ s.card • x s := by sorry
