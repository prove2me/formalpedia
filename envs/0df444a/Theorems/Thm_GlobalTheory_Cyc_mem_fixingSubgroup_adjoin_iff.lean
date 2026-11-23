-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_mem_fixingSubgroup_adjoin_iff
-- name    : GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:26.653028+00:00
-- url     : https://prove2.me/theorems/f27acde7-b6a5-41b6-826c-861d630d69d6
-- title:
--   Cyc: mem fixing Subgroup adjoin iff
-- statement:
--   The Cyc construction uses the mem fixing Subgroup adjoin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L96-L108

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff (S : Set (Om l)) (g : GQ l) :
    g ∈ (IntermediateField.adjoin ℚ_[l] S).fixingSubgroup ↔ ∀ x ∈ S, g x = x := by sorry
