-- Prove2me | Theorems.Thm_GlobalTheory_SkewLat_mem_scLat
-- name    : GlobalTheory.SkewLat.mem_scLat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:46.039172+00:00
-- url     : https://prove2.me/theorems/3f6aa7c0-d43f-4794-839a-dd149bf0107a
-- title:
--   Skew Lat: mem sc Lat
-- statement:
--   The Skew Lat construction uses the mem sc Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPairLat.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPairLat.lean#L18-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPairLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SkewLat
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.SkewLat.mem_scLat {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} :
    y ∈ scLat 𝔞 Λ ↔ ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ := by sorry
