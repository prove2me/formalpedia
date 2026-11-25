-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_power_sum
-- name    : GlobalTheory.Cyc.DiffSmall.exists_power_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:03:15.384837+00:00
-- url     : https://prove2.me/theorems/dda1404a-e9f3-5316-8c3e-b4090815bb6b
-- title:
--   Diff Small: exists power sum
-- statement:
--   The Diff Small construction uses the exists power sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L128-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L128-L148

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.DiffSmall.exists_power_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (r : ι → Om l)
    (hr : ∀ s ∈ S, ‖r s‖ ≤ 1) {s₀ : ι} (h₀ : s₀ ∈ S) :
    ∃ k : ℕ, ∏ t ∈ S.erase s₀, ‖r s₀ - r t‖ ≤ ‖∑ s ∈ S, r s ^ k‖ := by sorry
