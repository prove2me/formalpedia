-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_det_mul_mem
-- name    : GlobalTheory.SocleDet.det_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:30.592805+00:00
-- url     : https://prove2.me/theorems/96108aa5-34d5-40db-a6b6-565c4fbfeb57
-- title:
--   Socle Det: det mul mem
-- statement:
--   The Socle Det construction uses the det mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L21-L25

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

theorem GlobalTheory.SocleDet.det_mul_mem (I : Ideal R) (M : Matrix n n R) (x : n → R) (l : n)
    (h : ∀ r, (M *ᵥ x) r ∈ I) : M.det * x l ∈ I := by sorry
