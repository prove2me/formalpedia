-- Prove2me | Theorems.Thm_GlobalTheory_FormalInv_linearPart_map
-- name    : GlobalTheory.FormalInv.linearPart_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:13.299824+00:00
-- url     : https://prove2.me/theorems/ab827c3c-8a57-52ac-ae3c-662b01067842
-- title:
--   Formal Inv: linear Part map
-- statement:
--   The Formal Inv construction uses the linear Part map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/CoeffSubstInvMemOfTwoLeOrder.lean#L211-L213

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

theorem GlobalTheory.FormalInv.linearPart_map {S : Type*} [CommRing S] (φ : R →+* S) (u : ι → MvPowerSeries σ R) :
    linearPart (fun i => MvPowerSeries.map φ (u i)) = (linearPart u).map φ := by sorry
