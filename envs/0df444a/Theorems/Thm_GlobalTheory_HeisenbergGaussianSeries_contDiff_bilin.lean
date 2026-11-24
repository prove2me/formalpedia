-- Prove2me | Theorems.Thm_GlobalTheory_HeisenbergGaussianSeries_contDiff_bilin
-- name    : GlobalTheory.HeisenbergGaussianSeries.contDiff_bilin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:19:06.881997+00:00
-- url     : https://prove2.me/theorems/ab216fc2-ea06-4ba9-bb74-e9d2a943453a
-- title:
--   Heisenberg Gaussian Series: cont Diff bilin
-- statement:
--   The Heisenberg Gaussian Series construction uses the cont Diff bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousBicharacterWeilSetup.lean#L33-L40

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

theorem GlobalTheory.HeisenbergGaussianSeries.contDiff_bilin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) :
    ContDiff ℝ ∞ fun v : V => om v (J v) := by sorry
