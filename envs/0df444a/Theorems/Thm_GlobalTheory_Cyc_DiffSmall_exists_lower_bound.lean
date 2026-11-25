-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_DiffSmall_exists_lower_bound
-- name    : GlobalTheory.Cyc.DiffSmall.exists_lower_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:13:53.655625+00:00
-- url     : https://prove2.me/theorems/4472d911-34ec-4350-a12a-f885197c593e
-- title:
--   Diff Small: exists lower bound
-- statement:
--   The Diff Small construction uses the exists lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L305-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L305-L327

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

theorem GlobalTheory.Cyc.DiffSmall.exists_lower_bound {y : Om l} (hy : ‖y‖ ≤ 1) : ∃ c : ℝ, 0 < c ∧
    ∀ (x : Om l) (p : ℤ_[l][X]), ‖x‖ ≤ 1 → aeval x p = y → ∀ (T : Finset ℕ) (g : ℕ → GQ l),
      Set.InjOn (fun k => g k x) T → (∀ k ∈ T, g k y ≠ y) → c ≤ ∏ k ∈ T, ‖x - g k x‖ := by sorry
