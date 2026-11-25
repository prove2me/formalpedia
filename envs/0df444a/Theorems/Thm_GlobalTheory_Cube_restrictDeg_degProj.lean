-- Prove2me | Theorems.Thm_GlobalTheory_Cube_restrictDeg_degProj
-- name    : GlobalTheory.Cube.restrictDeg_degProj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:45:16.628457+00:00
-- url     : https://prove2.me/theorems/b300d7e6-3613-478a-a766-6e00ab920cc7
-- title:
--   Cube: restrict Deg deg Proj
-- statement:
--   The Cube construction uses the restrict Deg deg Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L69-L73

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

theorem GlobalTheory.Cube.restrictDeg_degProj (A : Cube.{v} ι R) (p q : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A p (degProj A q x) = if p = q then restrictDeg A p x else 0 := by sorry
