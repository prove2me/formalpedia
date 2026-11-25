-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_eOf_mulVec
-- name    : GlobalTheory.SgGlob.Iota.eOf_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:22.977491+00:00
-- url     : https://prove2.me/theorems/5dcf342e-e5d3-4afe-8785-fcadd14efc2e
-- title:
--   Iota: e Of mul Vec
-- statement:
--   The Iota construction uses the e Of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L147-L150

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
omit [NumberField E]

theorem GlobalTheory.SgGlob.Iota.eOf_mulVec (P : Matrix (Fin n) (Fin (r + 1)) E) (c : Fin r → E) :
    eOf P *ᵥ c = P *ᵥ (Fin.snoc c 0 : Fin (r + 1) → E) := by sorry
