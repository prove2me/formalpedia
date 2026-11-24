-- Prove2me | Theorems.Thm_GlobalTheory_LOneLower_wt_antitoneOn
-- name    : GlobalTheory.LOneLower.wt_antitoneOn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:56:01.000256+00:00
-- url     : https://prove2.me/theorems/52b332d9-14e4-4e09-971b-5c5d385d696f
-- title:
--   LOne Lower: wt antitone On
-- statement:
--   The LOne Lower construction uses the wt antitone On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L92-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLeNormLFunctionOne.lean#L92-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower

theorem GlobalTheory.LOneLower.wt_antitoneOn : AntitoneOn wt (Set.Ioi 0) := by sorry
