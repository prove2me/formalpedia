-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_AveragingRankOne_exists_reps
-- name    : GlobalTheory.Cyc.AveragingRankOne.exists_reps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:41.729547+00:00
-- url     : https://prove2.me/theorems/9fefecef-830b-483b-8593-7f763cef5417
-- title:
--   Averaging Rank One: exists reps
-- statement:
--   The Averaging Rank One construction uses the exists reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTateMaximalIdealKillsFirstCohomology.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicTateMaximalIdealKillsFirstCohomology.lean#L11-L31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AveragingRankOne

theorem GlobalTheory.Cyc.AveragingRankOne.exists_reps {G : Type*} [Group G] (H U V : Subgroup G) [U.FiniteIndex]
    (hV : ∀ g ∈ H, g ∈ V ↔ g ∈ U) :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ V := by sorry
