-- Prove2me | Theorems.Thm_GlobalTheory_Ex_QStr_root_over
-- name    : GlobalTheory.Ex.QStr.root_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:44.071313+00:00
-- url     : https://prove2.me/theorems/bf3cd8a9-648d-4a77-b14d-8ffabcf767d2
-- title:
--   QStr: root over
-- statement:
--   The QStr construction uses the root over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L132-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataTorsionStructureAlgClosed.lean#L132-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}

theorem GlobalTheory.Ex.QStr.root_over (hk : k ≠ 0) (γ : N.Gt) (b : N.A) (hb : b ^ k = γ.b) : ∃ γ' : N.Gt, γ'.b = b ∧ γ' ^ k = γ := by sorry
