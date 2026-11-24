-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_mulVec_mem_perpX
-- name    : GlobalTheory.SgGlob.mulVec_mem_perpX
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:09.205923+00:00
-- url     : https://prove2.me/theorems/1b24246d-f30c-47e5-a003-1d84b1be87af
-- title:
--   Sg Glob: mul Vec mem perp X
-- statement:
--   The Sg Glob construction uses the mul Vec mem perp X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L203-L209

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

theorem GlobalTheory.SgGlob.mulVec_mem_perpX {γ : Matrix (Fin n) (Fin n) E} (h : IsUn σ J γ)
    (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    γ *ᵥ v ∈ perpX σ J (γ * P) ↔ v ∈ perpX σ J P := by sorry
