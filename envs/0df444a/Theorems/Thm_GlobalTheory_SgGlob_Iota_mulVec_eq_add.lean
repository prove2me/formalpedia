-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_mulVec_eq_add
-- name    : GlobalTheory.SgGlob.Iota.mulVec_eq_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:58:29.612503+00:00
-- url     : https://prove2.me/theorems/37d8b0e8-1084-42ee-961c-f3967de592a6
-- title:
--   Iota: mul Vec eq add
-- statement:
--   The Iota construction uses the mul Vec eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L90-L92

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

theorem GlobalTheory.SgGlob.Iota.mulVec_eq_add (hg : (g : E) ≠ 0) (P P' : Matrix (Fin n) (Fin (r + 1)) E) (a : Fin (r + 1) → E) :
    P' *ᵥ a = P *ᵥ a + (g : E) • (((g : E)⁻¹ • (P' - P)) *ᵥ a) := by sorry
