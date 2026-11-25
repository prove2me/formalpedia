-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_moved
-- name    : GlobalTheory.Cyc.DiffSmall.exists_moved
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:03:15.933699+00:00
-- url     : https://prove2.me/theorems/0937ee4a-7b0f-5c6e-af68-1446c9a986e7
-- title:
--   Diff Small: exists moved
-- statement:
--   The Diff Small construction uses the exists moved property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L339-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L339-L428

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

theorem GlobalTheory.Cyc.DiffSmall.exists_moved (K : FinExt l) {y : Om l} (hy : ‖y‖ ≤ 1) (n : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 1) : ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ (E : IntermediateField ℚ_[l] (Om l))
      [FiniteDimensional ℚ_[l] E], Ks K i ≤ E → y ∈ E → ∀ S : Finset (GQ l), S.card ≤ n →
      (∀ s ∈ S, s ∈ Gj K i) → (∀ h ∈ Gj K i, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ E.fixingSubgroup) →
      ∃ x ∈ E, ‖x‖ ≤ 1 ∧ ∀ σ ∈ Gj K i, σ y ≠ y → δ ≤ ‖x - σ x‖ := by sorry
