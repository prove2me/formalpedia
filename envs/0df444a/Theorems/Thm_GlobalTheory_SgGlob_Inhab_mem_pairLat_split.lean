-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Inhab_mem_pairLat_split
-- name    : GlobalTheory.SgGlob.Inhab.mem_pairLat_split
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:37.870341+00:00
-- url     : https://prove2.me/theorems/94936366-a0fb-4620-b38a-eb2a9141827e
-- title:
--   Inhab: mem pair Lat split
-- statement:
--   The Inhab construction uses the mem pair Lat split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L315-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDifferentPair.lean#L315-L331

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

theorem GlobalTheory.SgGlob.Inhab.mem_pairLat_split (σ : E →+* E) {g : ℕ} (hg : g ≠ 0) (a b : E) (v : Fin 8 → E) :
    v ∈ pairLat g (splitP E) (splitQ σ g a b) ↔
      ∃ α ∈ dInv E 1, ∃ β ∈ Int' E, ∃ γ ∈ dInv E 1, ∃ δ ∈ Int' E,
        v = ![α, γ * splitC σ g a b, γ * a, γ * a, γ * b, γ * b, δ, β + δ] := by sorry
