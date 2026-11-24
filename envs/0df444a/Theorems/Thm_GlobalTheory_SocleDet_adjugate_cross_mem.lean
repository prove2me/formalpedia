-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_adjugate_cross_mem
-- name    : GlobalTheory.SocleDet.adjugate_cross_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:18:54.689905+00:00
-- url     : https://prove2.me/theorems/2f0a3d17-a223-4d83-82e0-cf64de72a64f
-- title:
--   Socle Det: adjugate cross mem
-- statement:
--   The Socle Det construction uses the adjugate cross mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L31-L42

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

theorem GlobalTheory.SocleDet.adjugate_cross_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (i j l : n)
    (h : ∀ r, r ≠ i → (M *ᵥ x) r ∈ I) :
    M.adjugate j i * x l - M.adjugate l i * x j ∈ I := by sorry
