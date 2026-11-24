-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_mem_genIn_of_map
-- name    : GlobalTheory.RegBound.mem_genIn_of_map
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:50.174984+00:00
-- url     : https://prove2.me/theorems/be960616-8463-4de2-837e-ed48045d370b
-- title:
--   Reg Bound: mem gen In of map
-- statement:
--   The Reg Bound construction uses the mem gen In of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L536-L542
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L536-L542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.RegBound.mem_genIn_of_map {I : Ideal (MvPolynomial σ K)} {e : ℕ} {F : MvPolynomial σ K}
    (h : map (algebraMap K L) F ∈ genIn (extIdeal L I) e) : F ∈ genIn I e := by sorry
