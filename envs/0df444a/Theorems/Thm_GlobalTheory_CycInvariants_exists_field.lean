-- Prove2me | Theorems.Thm_GlobalTheory_CycInvariants_exists_field
-- name    : GlobalTheory.CycInvariants.exists_field
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:18.726711+00:00
-- url     : https://prove2.me/theorems/f700874c-e413-4880-bb85-9d1a5fc0e468
-- title:
--   Cyc Invariants: exists field
-- statement:
--   The Cyc Invariants construction uses the exists field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerFixedIffMemCompletedIntegers.lean#L60-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTowerFixedIffMemCompletedIntegers.lean#L60-L86

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycInvariants
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.CycInvariants.exists_field (F : IntermediateField ℚ_[l] (Om l)) (x : Om l) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), x ∈ L ∧ F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) := by sorry
