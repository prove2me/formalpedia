-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_isSB_iff
-- name    : GlobalTheory.SW.Dict.isSB_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:16.984247+00:00
-- url     : https://prove2.me/theorems/568a0012-2a8d-4b7b-b943-f3a10cc83d34
-- title:
--   Dict: is SB iff
-- statement:
--   The Dict construction uses the is SB iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L128-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L128-L144

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
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem GlobalTheory.SW.Dict.isSB_iff (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    _root_.GlobalTheory.SW.IsSB φ ↔
      _root_.GlobalTheory.SW.IsSB (fun m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ =>
        φ (_root_.GlobalTheory.SW.ofQ m)) := by sorry
