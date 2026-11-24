-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_smul_eq
-- name    : GlobalTheory.SgGlob.Inhab.smul_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:25.603686+00:00
-- url     : https://prove2.me/theorems/903f71ea-82fc-4e0f-806f-127e6440e7dc
-- title:
--   Inhab: smul eq
-- statement:
--   The Inhab construction uses the smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L25-L25

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

theorem GlobalTheory.SgGlob.Inhab.smul_eq (c : 𝓞 E) (x : E) : c • x = algebraMap (𝓞 E) E c * x := by sorry
