-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_l_le
-- name    : GlobalTheory.Cyc.DiffSmall.norm_l_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:04.413961+00:00
-- url     : https://prove2.me/theorems/1a835d5d-23c9-49fd-9675-e96b81f40c6f
-- title:
--   Diff Small: norm l le
-- statement:
--   The Diff Small construction uses the norm l le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L217-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTraceNormGe.lean#L217-L237

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

theorem GlobalTheory.Cyc.DiffSmall.norm_l_le (j : ℕ) : ∀ η : Om l, η ^ l ^ j = 1 → η ≠ 1 → ‖(l : Om l)‖ ≤ ‖1 - η‖ := by sorry
