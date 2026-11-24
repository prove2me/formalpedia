-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_std
-- name    : GlobalTheory.SgGlob.Inhab.mem_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:56.300636+00:00
-- url     : https://prove2.me/theorems/467cce45-9288-4d55-beb5-c404947d7611
-- title:
--   Inhab: mem std
-- statement:
--   The Inhab construction uses the mem std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L35-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
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
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]

theorem GlobalTheory.SgGlob.Inhab.mem_std (v : Fin 2 → E) : v ∈ std E ↔ v 0 ∈ Int' E ∧ v 1 ∈ Int' E := by sorry
