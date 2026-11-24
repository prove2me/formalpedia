-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_mem_span_X_of_mul_X
-- name    : GlobalTheory.SocleDet.mem_span_X_of_mul_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:18:50.844953+00:00
-- url     : https://prove2.me/theorems/48b183bf-6e96-4646-90d6-8aeab4a17417
-- title:
--   Socle Det: mem span X of mul X
-- statement:
--   The Socle Det construction uses the mem span X of mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L157-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L157-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
open MvPowerSeries
variable {k : Type*} [CommRing k] {σ : Type*}

theorem GlobalTheory.SocleDet.mem_span_X_of_mul_X (S : Finset σ) (i : σ) (hi : i ∉ S) (p : MvPowerSeries σ k)
    (hp : p * X i ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S)) :
    p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by sorry
