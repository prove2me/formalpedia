-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_one_mem_UO
-- name    : GlobalTheory.SgGlob.one_mem_UO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:24.415705+00:00
-- url     : https://prove2.me/theorems/9332a173-c611-45a8-b04f-c0b1d8fc3441
-- title:
--   Sg Glob: one mem UO
-- statement:
--   The Sg Glob construction uses the one mem UO property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L345-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L345-L347

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

theorem GlobalTheory.SgGlob.one_mem_UO : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) ∈ UO E r := by sorry
