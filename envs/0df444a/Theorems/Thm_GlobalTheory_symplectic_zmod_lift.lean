-- Prove2me | Theorems.Thm_GlobalTheory_symplectic_zmod_lift
-- name    : GlobalTheory.symplectic_zmod_lift
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:41.6179+00:00
-- url     : https://prove2.me/theorems/6c27ce68-022d-4f7a-be3a-4cb215e2ac0c
-- title:
--   Global Theory: symplectic zmod lift
-- statement:
--   The Global Theory construction uses the symplectic zmod lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticZmodLift.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SymplecticZmodLift.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticZmodLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.symplectic_zmod_lift : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by sorry
