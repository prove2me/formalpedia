-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_IsRed_mem_iff
-- name    : GlobalTheory.SgGlob.IsRed.mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:26.599101+00:00
-- url     : https://prove2.me/theorems/5f9a0dc6-17b0-41a6-aa6c-3ee5ef54cb24
-- title:
--   Is Red: mem iff
-- statement:
--   The Is Red construction uses the mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L147-L151

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

theorem GlobalTheory.SgGlob.IsRed.mem_iff {Λ : Submodule (𝓞 E) (Fin n → E)} {P : Matrix (Fin n) (Fin (r + 1)) E} {x : Lz E m}
    {al : Matrix (Fin m) (Fin n) E} (h : IsRed σ J Jb Λ P x al) (y : Fin m → E) :
    y ∈ x.1 ↔ ∃ v ∈ latIn Λ (perpX σ J P), al *ᵥ v = y := by sorry
