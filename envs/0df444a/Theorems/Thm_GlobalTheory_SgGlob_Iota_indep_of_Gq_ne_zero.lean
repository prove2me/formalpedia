-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_indep_of_Gq_ne_zero
-- name    : GlobalTheory.SgGlob.Iota.indep_of_Gq_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:34.712298+00:00
-- url     : https://prove2.me/theorems/4e83e9c8-6207-4fd4-9564-72004e3d9a41
-- title:
--   Iota: indep of Gq ne zero
-- statement:
--   The Iota construction uses the indep of Gq ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L178-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L178-L230

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
omit [NumberField E]

theorem GlobalTheory.SgGlob.Iota.indep_of_Gq_ne_zero (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {T T' : E}
    {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
    (h : (P, P') ∈ XZ σ J T T' Z) (hG : Gq σ T T' Z ≠ 0) (a a' : Fin (r + 1) → E)
    (e : P *ᵥ a + P' *ᵥ a' = 0) : a = 0 ∧ a' = 0 := by sorry
