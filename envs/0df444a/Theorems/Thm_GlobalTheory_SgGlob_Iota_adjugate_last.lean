-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_adjugate_last
-- name    : GlobalTheory.SgGlob.Iota.adjugate_last
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:24.524981+00:00
-- url     : https://prove2.me/theorems/9dc8957a-13bf-4181-ae70-621ef975b31c
-- title:
--   Iota: adjugate last
-- statement:
--   The Iota construction uses the adjugate last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L158-L161

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

theorem GlobalTheory.SgGlob.Iota.adjugate_last (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Z.adjugate (Fin.last r) (Fin.last r) = lead Z r (Nat.le_succ r) := by sorry
