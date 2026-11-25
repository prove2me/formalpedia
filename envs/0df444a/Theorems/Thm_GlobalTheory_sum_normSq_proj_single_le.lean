-- Prove2me | Theorems.Thm_GlobalTheory_sum_normSq_proj_single_le
-- name    : GlobalTheory.sum_normSq_proj_single_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:55:52.85278+00:00
-- url     : https://prove2.me/theorems/e4721855-f4d4-425d-b4f6-f18d00ede76e
-- title:
--   Global Theory: sum norm Sq proj single le
-- statement:
--   The Global Theory construction uses the sum norm Sq proj single le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumNormSqProjectionsTensorUnitaryGlLe.lean#L15-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumNormSqProjectionsTensorUnitaryGlLe.lean#L15-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasEigenvalueSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantHermitianFormNonnegOfCloudEigenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormHhJSelfLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CloudNodeProjectionNormLowLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumNormSqProjectionsTensorUnitaryGlLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.sum_normSq_proj_single_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ s, ‖pr s (Pi.single c w)‖ ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) * ‖w‖ ^ 2 := by sorry
