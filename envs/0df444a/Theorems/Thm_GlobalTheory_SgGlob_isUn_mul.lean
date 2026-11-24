-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_isUn_mul
-- name    : GlobalTheory.SgGlob.isUn_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:29.946322+00:00
-- url     : https://prove2.me/theorems/95c2547f-10ec-4e65-bb3a-93d6e10e02a5
-- title:
--   Sg Glob: is Un mul
-- statement:
--   The Sg Glob construction uses the is Un mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L248-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L248-L252

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

theorem GlobalTheory.SgGlob.isUn_mul {γ δ : Matrix (Fin n) (Fin n) E} (hγ : IsUn σ J γ) (hδ : IsUn σ J δ) :
    IsUn σ J (γ * δ) := by sorry
