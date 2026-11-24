-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_SquareTheorem_isSquare_of_norm_sub_one_lt
-- name    : GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:13:54.89809+00:00
-- url     : https://prove2.me/theorems/afc55fec-19e7-4a13-9061-e01f70b9b9d5
-- title:
--   Square Theorem: is Square of norm sub one lt
-- statement:
--   The Square Theorem construction uses the is Square of norm sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareOfValuedSubOneLt.lean#L12-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSquareOfValuedSubOneLt.lean#L12-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.SquareTheorem
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.SquareTheorem.isSquare_of_norm_sub_one_lt {K : Type*} [NormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (x : K) (h : ‖x - 1‖ < ‖(4 : K)‖) : IsSquare x := by sorry
