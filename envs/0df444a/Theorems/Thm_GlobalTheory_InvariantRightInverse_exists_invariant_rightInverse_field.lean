-- Prove2me | Theorems.Thm_GlobalTheory_InvariantRightInverse_exists_invariant_rightInverse_field
-- name    : GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse_field
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:04.418304+00:00
-- url     : https://prove2.me/theorems/4868df37-6b9d-4ef2-95a5-9ad61d22eb18
-- title:
--   Invariant Right Inverse: exists invariant right Inverse field
-- statement:
--   The Invariant Right Inverse construction uses the exists invariant right Inverse field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInvariantRightInverseField.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInvariantRightInverseField.lean#L38-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantRightInverseField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantRightInverse

theorem GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse_field {L : Type} [Field L] (G : Type)
    (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq b]
    (κ : Matrix b N L) (Y : Matrix N b L) (h : κ * Y = 1)
    (hκ : ∀ g : G, Matrix.map κ (⇑(act g) : L → L) = κ) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g : G, Matrix.map Λ (⇑(act g) : L → L) = Λ := by sorry
