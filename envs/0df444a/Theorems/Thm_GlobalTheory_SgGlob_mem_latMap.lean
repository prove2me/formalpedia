-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_mem_latMap
-- name    : GlobalTheory.SgGlob.mem_latMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:06.637637+00:00
-- url     : https://prove2.me/theorems/8d17d755-a524-446b-8236-885d0514eb71
-- title:
--   Sg Glob: mem lat Map
-- statement:
--   The Sg Glob construction uses the mem lat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L142-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L142-L143

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

theorem GlobalTheory.SgGlob.mem_latMap (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E) :
    v ∈ latMap γ Λ ↔ ∃ w ∈ Λ, γ *ᵥ w = v := by sorry
