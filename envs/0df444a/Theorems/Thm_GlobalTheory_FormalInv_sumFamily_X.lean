-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_sumFamily_X
-- name    : GlobalTheory.FormalInv.sumFamily_X
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:34:35.230314+00:00
-- url     : https://prove2.me/theorems/c9b82a11-1abb-4c51-a26a-d9b2596d0f06
-- title:
--   Formal Inv: sum Family X
-- statement:
--   The Formal Inv construction uses the sum Family X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L650-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L650-L652

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}

theorem GlobalTheory.FormalInv.sumFamily_X [Finite σ] [Finite σ'] (s : σ ⊕ σ') :
    sumFamily (fun i : σ => (X i : MvPowerSeries σ R)) (fun j : σ' => X j) s = X s := by sorry
