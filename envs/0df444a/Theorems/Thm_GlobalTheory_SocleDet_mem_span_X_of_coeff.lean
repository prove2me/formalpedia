-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_mem_span_X_of_coeff
-- name    : GlobalTheory.SocleDet.mem_span_X_of_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:24.069223+00:00
-- url     : https://prove2.me/theorems/4bccef17-3b43-4572-a9cb-b1336f2c46a3
-- title:
--   Socle Det: mem span X of coeff
-- statement:
--   The Socle Det construction uses the mem span X of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L130-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L130-L155

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

theorem GlobalTheory.SocleDet.mem_span_X_of_coeff (S : Finset σ) : ∀ p : MvPowerSeries σ k,
    (∀ m : σ →₀ ℕ, (∀ j ∈ S, m j = 0) → coeff m p = 0) →
      p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k)) '' S) := by sorry
