-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_mem_frameLat
-- name    : GlobalTheory.SgGlob.Iota.mem_frameLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:23.358253+00:00
-- url     : https://prove2.me/theorems/fd55fe55-684a-4287-ab56-0890f0c8734a
-- title:
--   Iota: mem frame Lat
-- statement:
--   The Iota construction uses the mem frame Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L39-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L39-L67

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

theorem GlobalTheory.SgGlob.Iota.mem_frameLat (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ frameLat P ↔ ∃ a : Fin (r + 1) → E, (∀ b : Fin (r + 1), a b ∈ dInv E (r - (b : ℕ))) ∧ P *ᵥ a = v := by sorry
