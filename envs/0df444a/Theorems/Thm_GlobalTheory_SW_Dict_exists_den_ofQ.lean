-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_exists_den_ofQ
-- name    : GlobalTheory.SW.Dict.exists_den_ofQ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:47.994423+00:00
-- url     : https://prove2.me/theorems/767a5944-b3a4-457a-a5ee-d4b65e223171
-- title:
--   Dict: exists den of Q
-- statement:
--   The Dict construction uses the exists den of Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L87-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L87-L96

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

theorem GlobalTheory.SW.Dict.exists_den_ofQ : ∃ D : ℕ, 0 < D ∧
    ∀ m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ, _root_.GlobalTheory.SW.IntM m →
    _root_.GlobalTheory.SW.IntM (D • _root_.GlobalTheory.SW.Dict.ofQEquiv E n N m) := by sorry
