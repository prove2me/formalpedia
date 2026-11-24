-- Prove2me | Theorems.Thm_GlobalTheory_isBigO_exp_neg_div_rpow
-- name    : GlobalTheory.isBigO_exp_neg_div_rpow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:40.917022+00:00
-- url     : https://prove2.me/theorems/c369f137-cd5c-4fb5-87a9-fc3ff59ce092
-- title:
--   Global Theory: is Big O exp neg div rpow
-- statement:
--   The Global Theory construction uses the is Big O exp neg div rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L75-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology

theorem GlobalTheory.isBigO_exp_neg_div_rpow {c : ℝ} (hc : 0 < c) (b : ℝ) :
    (fun t : ℝ => Real.exp (-c / t)) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by sorry
