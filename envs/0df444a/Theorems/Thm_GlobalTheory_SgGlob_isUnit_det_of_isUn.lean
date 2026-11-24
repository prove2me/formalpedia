-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_isUnit_det_of_isUn
-- name    : GlobalTheory.SgGlob.isUnit_det_of_isUn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:18.069806+00:00
-- url     : https://prove2.me/theorems/dccdf619-294e-4024-8a06-657c7ee30af5
-- title:
--   Sg Glob: is Unit det of is Un
-- statement:
--   The Sg Glob construction uses the is Unit det of is Un property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L195-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L195-L199

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
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]

theorem GlobalTheory.SgGlob.isUnit_det_of_isUn {γ : Matrix (Fin n) (Fin n) E} (hJ : IsUnit J.det) (h : IsUn σ J γ) :
    IsUnit γ.det := by sorry
