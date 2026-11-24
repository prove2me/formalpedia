-- Prove2me | Theorems.Thm_GlobalTheory_gram_det_eq_zero_of_lt_card
-- name    : GlobalTheory.gram_det_eq_zero_of_lt_card
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:54.232736+00:00
-- url     : https://prove2.me/theorems/fa0063ee-c2c0-4d3b-ad8d-0255acec8520
-- title:
--   Global Theory: gram det eq zero of lt card
-- statement:
--   The Global Theory construction uses the gram det eq zero of lt card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsScalarSubPosSemidef.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsScalarSubPosSemidef.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.gram_det_eq_zero_of_lt_card {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Matrix (Fin r) ι ℂ) (h : r < Fintype.card ι) : (Nᴴ * N).det = 0 := by sorry
