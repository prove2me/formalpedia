-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_normalize
-- name    : GlobalTheory.PMonE.normalize
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:42:28.749074+00:00
-- url     : https://prove2.me/theorems/55fe5451-4a38-4b38-82f0-5062024aad2f
-- title:
--   PMon E: normalize
-- statement:
--   The PMon E construction uses the normalize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusPolydiscWindowsSurjectiveBoundsZero.lean#L45-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusPolydiscWindowsSurjectiveBoundsZero.lean#L45-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWindowRadii
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaAllOrdersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusWindowSeriesTermNormLeRowBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMonoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowSummedRowPowEqAdditiveSystemPowerSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosEqIntegralAdditiveSystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPolydiscWindowsSurjectiveBoundsZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset Matrix

theorem GlobalTheory.PMonE.normalize {F : Type} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hlam : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hanti : Antitone (fun j => ‖lam j‖)) (horth : Orth p lam) (L U : ℕ) (hL : 1 ≤ L)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    ∃ M : ℕ → Matrix (Fin h) (Fin h) F, Normal L M ∧ (M 0).det ≠ 0 ∧
      ∃ Φ : (Fin h → F) → (Fin h → F), (∀ b, (∀ r, ‖b r‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖) → Integral (Φ b)) ∧
        Φ 0 = 0 ∧ ∀ z b, gsum (p ^ h) (L + U) M z = Φ b ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = b r := by sorry
