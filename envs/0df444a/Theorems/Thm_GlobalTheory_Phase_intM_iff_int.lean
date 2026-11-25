-- Prove2me | Theorems.Thm_GlobalTheory_Phase_intM_iff_int
-- name    : GlobalTheory.Phase.intM_iff_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:23.512243+00:00
-- url     : https://prove2.me/theorems/f9d6c22a-0781-4d82-b20c-006f78f2527b
-- title:
--   Phase: int M iff int
-- statement:
--   The Phase construction uses the int M iff int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IntMIffInt.lean#L104-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}
omit [Fintype κ] [Fintype ι]

theorem GlobalTheory.Phase.intM_iff_int {x : Matrix κ ι ℚ} : IntM x ↔ ∀ k i, ∃ z : ℤ, x k i = z := by sorry
