-- Prove2me | Theorems.Thm_GlobalTheory_ClassWeight_exists_evalChar_ne
-- name    : GlobalTheory.ClassWeight.exists_evalChar_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:03.91068+00:00
-- url     : https://prove2.me/theorems/592b79c3-a11f-412f-902b-ff83b29ff388
-- title:
--   Class Weight: exists eval Char ne
-- statement:
--   The Class Weight construction uses the exists eval Char ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ClassSubStructure.lean#L26-L52

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

theorem GlobalTheory.ClassWeight.exists_evalChar_ne [Module.Finite ℤ X] [IsAlgClosed F] (hN : (N : F) ≠ 0) {α β : X}
    (h : ¬ ∃ mu, β = α + N • mu) : ∃ τ : TorChar X F N, evalChar F N β τ ≠ evalChar F N α τ := by sorry
