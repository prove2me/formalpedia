-- Prove2me | Theorems.Thm_GlobalTheory_Cube_restrictDeg_apply
-- name    : GlobalTheory.Cube.restrictDeg_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:35.373073+00:00
-- url     : https://prove2.me/theorems/39d090c9-e19f-4ab6-95bc-298142895454
-- title:
--   Cube: restrict Deg apply
-- statement:
--   The Cube construction uses the restrict Deg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L43-L44

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

theorem GlobalTheory.Cube.restrictDeg_apply (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s)
    (s : {s : Finset ι // s.card = p}) : restrictDeg A p x s = x s.1 := by sorry
