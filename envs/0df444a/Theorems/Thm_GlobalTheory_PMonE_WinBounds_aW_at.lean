-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_WinBounds_aW_at
-- name    : GlobalTheory.PMonE.WinBounds.aW_at
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:25.135691+00:00
-- url     : https://prove2.me/theorems/496600c9-d40b-431a-a009-58371e5dc1e8
-- title:
--   Win Bounds: a W at
-- statement:
--   The Win Bounds construction uses the a W at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusWindowSeriesTermNormLeRowBound.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusWindowSeriesTermNormLeRowBound.lean#L75-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusWindowSeriesTermNormLeRowBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.WinBounds
open GlobalTheory.PMonE
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem GlobalTheory.PMonE.WinBounds.aW_at (k : ℕ) (lam : Fin (k + 1) → F) (j : Fin (k + 1)) (m : ℤ) :
    aW p k lam (((j : ℕ) : ℤ) + ((k : ℤ) + 1) * m) = ‖lam j‖ * (p : ℝ) ^ (-m) := by sorry
