-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_norm_pw_mono
-- name    : GlobalTheory.PMonE.norm_pw_mono
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:12.176474+00:00
-- url     : https://prove2.me/theorems/a79b99a0-e1d0-4c93-80d3-6af2d316e5aa
-- title:
--   PMon E: norm pw mono
-- statement:
--   The PMon E construction uses the norm pw mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormFrobeniusWindowSeriesTermMono.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormFrobeniusWindowSeriesTermMono.lean#L15-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormFrobeniusWindowSeriesTermMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
open GlobalTheory GlobalTheory.PMonE

theorem GlobalTheory.PMonE.norm_pw_mono {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℤ) (y y' : F) (hy : ‖y‖ ≤ ‖y'‖) : ‖pw p k y‖ ≤ ‖pw p k y'‖ := by sorry
