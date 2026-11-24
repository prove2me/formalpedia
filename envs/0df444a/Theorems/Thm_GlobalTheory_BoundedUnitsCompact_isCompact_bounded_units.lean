-- Prove2me | Theorems.Thm_GlobalTheory_BoundedUnitsCompact_isCompact_bounded_units
-- name    : GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:15.268829+00:00
-- url     : https://prove2.me/theorems/6b2c17f0-9f8c-4cff-94b3-658a65817f44
-- title:
--   Bounded Units Compact: is Compact bounded units
-- statement:
--   The Bounded Units Compact construction uses the is Compact bounded units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedEntriesIsCompact.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedEntriesIsCompact.lean#L18-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BoundedEntriesIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedUnitsCompact

theorem GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] {n : ℕ} [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ (i j : Fin n), ‖(↑g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ (i j : Fin n), ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by sorry
