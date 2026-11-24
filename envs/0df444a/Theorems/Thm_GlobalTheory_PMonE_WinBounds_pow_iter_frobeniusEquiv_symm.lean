-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_WinBounds_pow_iter_frobeniusEquiv_symm
-- name    : GlobalTheory.PMonE.WinBounds.pow_iter_frobeniusEquiv_symm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:32.879638+00:00
-- url     : https://prove2.me/theorems/8481ce7d-7575-4630-8129-5b4495991559
-- title:
--   Win Bounds: pow iter frobenius Equiv symm
-- statement:
--   The Win Bounds construction uses the pow iter frobenius Equiv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusWindowSeriesTermNormLeRowBound.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FrobeniusWindowSeriesTermNormLeRowBound.lean#L12-L20

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

theorem GlobalTheory.PMonE.WinBounds.pow_iter_frobeniusEquiv_symm {F : Type} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (x : F) (m : ℕ) : (((frobeniusEquiv F p).symm)^[m] x) ^ p ^ m = x := by sorry
