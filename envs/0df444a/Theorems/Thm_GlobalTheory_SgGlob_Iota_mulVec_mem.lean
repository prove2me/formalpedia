-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_mulVec_mem
-- name    : GlobalTheory.SgGlob.Iota.mulVec_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:47.502299+00:00
-- url     : https://prove2.me/theorems/5a5533a5-2ca2-411d-8f77-00b0df3356e2
-- title:
--   Iota: mul Vec mem
-- statement:
--   The Iota construction uses the mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L119-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndepOfGqNeZero
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
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Iota
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}

theorem GlobalTheory.SgGlob.Iota.mulVec_mem (hg : (g : E) ≠ 0) (hΛ : pairLat g P P' ≤ Λ) {a : Fin (r + 1) → E}
    (ha : ∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) :
    P *ᵥ a ∈ Λ ∧ P' *ᵥ a ∈ Λ ∧ P' *ᵥ a - P *ᵥ a ∈ mulLat g Λ := by sorry
