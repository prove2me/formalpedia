-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_Iota_det_mul_last
-- name    : GlobalTheory.SgGlob.Iota.det_mul_last
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:01.198697+00:00
-- url     : https://prove2.me/theorems/4d6e00e1-bb55-4534-90ef-80dc6fccb108
-- title:
--   Iota: det mul last
-- statement:
--   The Iota construction uses the det mul last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L165-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndepOfGqNeZero.lean#L165-L174

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

theorem GlobalTheory.SgGlob.Iota.det_mul_last {T : E} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E} {x y : Fin (r + 1) → E}
    (h : TF r T *ᵥ y + Z *ᵥ x = 0) :
    Z.det * x (Fin.last r) = T * lead Z r (Nat.le_succ r) * y (Fin.last r) := by sorry
