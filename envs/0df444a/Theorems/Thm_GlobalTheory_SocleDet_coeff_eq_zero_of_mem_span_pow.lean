-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_coeff_eq_zero_of_mem_span_pow
-- name    : GlobalTheory.SocleDet.coeff_eq_zero_of_mem_span_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:25.330662+00:00
-- url     : https://prove2.me/theorems/c9f0de1b-1c86-47d4-bd72-91e0eec57263
-- title:
--   Socle Det: coeff eq zero of mem span pow
-- statement:
--   The Socle Det construction uses the coeff eq zero of mem span pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L121-L128

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

theorem GlobalTheory.SocleDet.coeff_eq_zero_of_mem_span_pow (N : ℕ) (S : Set σ) (p : MvPowerSeries σ k)
    (hp : p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k) ^ N) '' S))
    (m : σ →₀ ℕ) (hm : ∀ j ∈ S, m j < N) : coeff m p = 0 := by sorry
