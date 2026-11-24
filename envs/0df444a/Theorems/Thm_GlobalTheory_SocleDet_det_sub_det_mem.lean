-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_det_sub_det_mem
-- name    : GlobalTheory.SocleDet.det_sub_det_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:18:41.702348+00:00
-- url     : https://prove2.me/theorems/f1c93902-98a4-4055-8c55-e5587178d331
-- title:
--   Socle Det: det sub det mem
-- statement:
--   The Socle Det construction uses the det sub det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L70-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L70-L111

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
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.SocleDet.det_sub_det_mem (I : Ideal R) (x : n → R)
    (hx : ∀ (S : Finset n) (i : n), i ∉ S → ∀ p : R, p * x i ∈ Ideal.span (x '' S) →
      p ∈ Ideal.span (x '' S))
    (c c' : Matrix n n R) (h : c *ᵥ x = c' *ᵥ x) (hI : ∀ r, (c *ᵥ x) r ∈ I) :
    c'.det - c.det ∈ I := by sorry
