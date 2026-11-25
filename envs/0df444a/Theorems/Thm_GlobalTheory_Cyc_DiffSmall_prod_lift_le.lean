-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_DiffSmall_prod_lift_le
-- name    : GlobalTheory.Cyc.DiffSmall.prod_lift_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:13.010332+00:00
-- url     : https://prove2.me/theorems/c4539a28-f66e-47f1-9a79-df826b84d26e
-- title:
--   Diff Small: prod lift le
-- statement:
--   The Diff Small construction uses the prod lift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L239-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L239-L294

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

theorem GlobalTheory.Cyc.DiffSmall.prod_lift_le (F E : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ F.fixingSubgroup)
    (hu : ∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ E.fixingSubgroup)
    {x : Om l} (hxE : x ∈ E) (hx : ‖x‖ ≤ 1) (τ : GQ l) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hτ : ∀ z ∈ F, ‖z‖ ≤ 1 → ‖τ z - z‖ ≤ ρ) : ∏ s ∈ S, ‖x - τ (s x)‖ ≤ ρ := by sorry
