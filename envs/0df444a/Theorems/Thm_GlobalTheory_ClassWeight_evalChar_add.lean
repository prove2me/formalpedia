-- Prove2me | Theorems.Thm_GlobalTheory_ClassWeight_evalChar_add
-- name    : GlobalTheory.ClassWeight.evalChar_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:43.150632+00:00
-- url     : https://prove2.me/theorems/64d075ed-461d-411d-aecb-fd37acaeed0f
-- title:
--   Class Weight: eval Char add
-- statement:
--   The Class Weight construction uses the eval Char add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L18-L19

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

theorem GlobalTheory.ClassWeight.evalChar_add (α β : X) (τ : TorChar X F N) :
    evalChar F N (α + β) τ = evalChar F N α τ * evalChar F N β τ := by sorry
