-- Prove2me | Theorems.Thm_GlobalTheory_SgGlob_col_mem_perpX
-- name    : GlobalTheory.SgGlob.col_mem_perpX
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:54:43.168224+00:00
-- url     : https://prove2.me/theorems/5dde1309-0dfa-4cca-a86f-74a54db5f340
-- title:
--   Sg Glob: col mem perp X
-- statement:
--   The Sg Glob construction uses the col mem perp X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean#L155-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
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
open GlobalTheory GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E]

theorem GlobalTheory.SgGlob.col_mem_perpX {T : E} {P : Matrix (Fin n) (Fin (r + 1)) E} (h : IsFrame σ J T P)
    (b : Fin (r + 1)) : (fun i => P i b) ∈ perpX σ J P := by sorry
