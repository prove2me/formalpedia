-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_intM_nsmul
-- name    : GlobalTheory.SW.Dict.intM_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:23.532427+00:00
-- url     : https://prove2.me/theorems/d9ac6043-c82a-48a8-9b79-0edbef435b44
-- title:
--   Dict: int M nsmul
-- statement:
--   The Dict construction uses the int M nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.Dict.intM_nsmul {K κ ι : Type} [Field K] (R : ℕ) {x : Matrix κ ι K}
    (h : _root_.GlobalTheory.SW.IntM x) :
    _root_.GlobalTheory.SW.IntM (R • x) := by sorry
