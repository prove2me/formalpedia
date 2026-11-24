-- Prove2me | Theorems.Thm_GlobalTheory_InvariantRightInverse_exists_invariant_rightInverse
-- name    : GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:19.35626+00:00
-- url     : https://prove2.me/theorems/5a9636ea-055a-4703-8c7f-b4d1758ff3e6
-- title:
--   Invariant Right Inverse: exists invariant right Inverse
-- statement:
--   The Invariant Right Inverse construction uses the exists invariant right Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInvariantRightInverseField.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInvariantRightInverseField.lean#L55-L59

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

theorem GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse :
    ∀ (L : Type) [inst : CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [inst_1 : Fintype N] [DecidableEq N] [Fintype b] [inst_4 : DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = (1 : Matrix b b L) → (∀ (g : G), Matrix.map κ (⇑(act g) : L → L) = κ) → ∃ (Λ : Matrix N b L), κ * Λ = (1 : Matrix b b L) ∧ ∀ (g : G), Matrix.map Λ (⇑(act g) : L → L) = Λ := by sorry
