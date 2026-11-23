-- Prove2me | Theorems.Thm_GlobalTheory_ClassWeight_evalChar_add_nsmul
-- name    : GlobalTheory.ClassWeight.evalChar_add_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:29.817771+00:00
-- url     : https://prove2.me/theorems/3cef1cb4-6554-4c55-87f4-4e3c4f58e3dd
-- title:
--   Class Weight: eval Char add nsmul
-- statement:
--   The Class Weight construction uses the eval Char add nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L21-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}

theorem GlobalTheory.ClassWeight.evalChar_add_nsmul (α mu : X) (τ : TorChar X F N) : evalChar F N (α + N • mu) τ = evalChar F N α τ := by sorry
