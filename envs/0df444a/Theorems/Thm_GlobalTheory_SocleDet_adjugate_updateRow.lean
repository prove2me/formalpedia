-- Prove2me | Theorems.Thm_GlobalTheory_SocleDet_adjugate_updateRow
-- name    : GlobalTheory.SocleDet.adjugate_updateRow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:14.597686+00:00
-- url     : https://prove2.me/theorems/fd48dfe4-a030-4759-80f1-cf90d6d631c7
-- title:
--   Socle Det: adjugate update Row
-- statement:
--   The Socle Det construction uses the adjugate update Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean#L27-L29

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

theorem GlobalTheory.SocleDet.adjugate_updateRow (M : Matrix n n R) (i l : n) (v : n → R) :
    (M.updateRow i v).adjugate l i = M.adjugate l i := by sorry
