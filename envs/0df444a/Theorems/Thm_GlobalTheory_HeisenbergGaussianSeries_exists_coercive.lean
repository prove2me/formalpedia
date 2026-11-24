-- Prove2me | Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_exists_coercive
-- name    : GlobalTheory.HeisenbergGaussianSeries.exists_coercive
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:34.687101+00:00
-- url     : https://prove2.me/theorems/aa55f88e-f0f0-478e-9b23-5072925389e2
-- title:
--   Heisenberg Gaussian Series: exists coercive
-- statement:
--   The Heisenberg Gaussian Series construction uses the exists coercive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosMulNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousBicharacterWeilSetup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.HeisenbergGaussianSeries

theorem GlobalTheory.HeisenbergGaussianSeries.exists_coercive {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ om v (J v) := by sorry
