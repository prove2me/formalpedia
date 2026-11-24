-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_norm_eq_of_norm_sub_lt
-- name    : GlobalTheory.NormUnits.norm_eq_of_norm_sub_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:14.593144+00:00
-- url     : https://prove2.me/theorems/de184255-7d4b-4509-a788-6cb96f30e1c4
-- title:
--   Norm Units: norm eq of norm sub lt
-- statement:
--   The Norm Units construction uses the norm eq of norm sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMulStarEqOfNormOneUnramifiedQuadratic.lean#L13-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.NormUnits

theorem GlobalTheory.NormUnits.norm_eq_of_norm_sub_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K} (h : ‖x - y‖ < ‖y‖) :
    ‖x‖ = ‖y‖ := by sorry
