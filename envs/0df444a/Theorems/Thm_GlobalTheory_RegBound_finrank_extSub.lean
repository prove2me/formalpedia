-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_finrank_extSub
-- name    : GlobalTheory.RegBound.finrank_extSub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:12.861606+00:00
-- url     : https://prove2.me/theorems/c3b6b08b-c1df-47a8-a0a2-6fb3f2426d44
-- title:
--   Reg Bound: finrank ext Sub
-- statement:
--   The Reg Bound construction uses the finrank ext Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L473-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L473-L520

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

theorem GlobalTheory.RegBound.finrank_extSub (W : Submodule K (MvPolynomial σ K)) [Module.Finite K W] :
    finrank L (extSub L W) = finrank K W := by sorry
