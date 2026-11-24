-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_UO_entry_mem
-- name    : GlobalTheory.SgGlob.UO.entry_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:46.198815+00:00
-- url     : https://prove2.me/theorems/9220cfe7-cbb2-49d4-b679-3e8a36a6a3bc
-- title:
--   UO: entry mem
-- statement:
--   The UO construction uses the entry mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L336-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L336-L343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {n r : ℕ}

theorem GlobalTheory.SgGlob.UO.entry_mem {u : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : u ∈ UO E r) (a b : Fin (r + 1)) :
    u a b ∈ dInv E ((b : ℕ) - a) := by sorry
