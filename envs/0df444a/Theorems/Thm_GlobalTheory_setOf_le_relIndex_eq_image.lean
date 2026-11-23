-- Prove2me | Theorems.Thm_GlobalTheory_setOf_le_relIndex_eq_image
-- name    : GlobalTheory.setOf_le_relIndex_eq_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:36.673204+00:00
-- url     : https://prove2.me/theorems/04a26cb0-8d55-45aa-a381-985834e471a5
-- title:
--   Global Theory: set Of le rel Index eq image
-- statement:
--   The Global Theory construction uses the set Of le rel Index eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe.lean#L71-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {M : Type*} [AddCommGroup M]

theorem GlobalTheory.setOf_le_relIndex_eq_image (K : AddSubgroup M) (m : ℕ) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m} =
      (fun H' : AddSubgroup K => H'.map K.subtype) '' {H' | H'.index = m} := by sorry
