-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_mul_mem_dInv
-- name    : GlobalTheory.SgGlob.mul_mem_dInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:35.475094+00:00
-- url     : https://prove2.me/theorems/89127c4a-3e42-4059-b12e-f826dbbf4c11
-- title:
--   Sg Glob: mul mem d Inv
-- statement:
--   The Sg Glob construction uses the mul mem d Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L331-L334

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

theorem GlobalTheory.SgGlob.mul_mem_dInv {i j : ℕ} {a b : E} (ha : a ∈ dInv E i) (hb : b ∈ dInv E j) :
    a * b ∈ dInv E (i + j) := by sorry
