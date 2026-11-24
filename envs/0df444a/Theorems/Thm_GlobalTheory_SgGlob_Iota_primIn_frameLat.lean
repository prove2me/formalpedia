-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_primIn_frameLat
-- name    : GlobalTheory.SgGlob.Iota.primIn_frameLat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:23.885015+00:00
-- url     : https://prove2.me/theorems/b2e46e20-3f46-4aa9-86a5-a985f885be1c
-- title:
--   Iota: prim In frame Lat
-- statement:
--   The Iota construction uses the prim In frame Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L130-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L130-L143

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

theorem GlobalTheory.SgGlob.Iota.primIn_frameLat (hg : (g : E) ≠ 0) (hΛ : PrimIn (pairLat g P P') Λ)
    (hind : ∀ a a', P *ᵥ a + P' *ᵥ a' = 0 → a = 0 ∧ a' = 0) :
    PrimIn (frameLat P) Λ ∧ PrimIn (frameLat P') Λ := by sorry
