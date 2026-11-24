-- Prove2me | Theorems.Thm_GlobalTheory_BoundedUnitsCompact_boundedEntries_isCompact
-- name    : GlobalTheory.BoundedUnitsCompact.boundedEntries_isCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:01:38.294594+00:00
-- url     : https://prove2.me/theorems/53d006ba-4eb7-41aa-9b45-64e012da8dda
-- title:
--   Bounded Units Compact: bounded Entries is Compact
-- statement:
--   The Bounded Units Compact construction uses the bounded Entries is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedEntriesIsCompact.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BoundedEntriesIsCompact.lean#L5-L16

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

theorem GlobalTheory.BoundedUnitsCompact.boundedEntries_isCompact {F : Type} [NontriviallyNormedField F] [ProperSpace F] {n : ℕ}
    (M : ℝ) : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ M} := by sorry
