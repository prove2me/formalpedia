-- Prove2me | Theorems.Thm_GlobalTheory_SW_ind_isSB
-- name    : GlobalTheory.SW.ind_isSB
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:48.911044+00:00
-- url     : https://prove2.me/theorems/fd9fa8ce-defb-5aff-9ec5-7e272179306d
-- title:
--   SW: ind is SB
-- statement:
--   The SW construction uses the ind is SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TestFunctionWitness.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TestFunctionWitness.lean#L24-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TestFunctionWitness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory GlobalTheory.SW
open Classical

theorem GlobalTheory.SW.ind_isSB {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    IsSB (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := by sorry
