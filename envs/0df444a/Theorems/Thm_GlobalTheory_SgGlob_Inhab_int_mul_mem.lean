-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_int_mul_mem
-- name    : GlobalTheory.SgGlob.Inhab.int_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:41.178282+00:00
-- url     : https://prove2.me/theorems/f84b6f8d-0fdb-4ea9-b664-710e616f6b7c
-- title:
--   Inhab: int mul mem
-- statement:
--   The Inhab construction uses the int mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L213-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L213-L217

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

theorem GlobalTheory.SgGlob.Inhab.int_mul_mem {I : FractionalIdeal (𝓞 E)⁰ E} {c x : E} (hc : c ∈ Int' E) (hx : x ∈ I) :
    c * x ∈ I := by sorry
