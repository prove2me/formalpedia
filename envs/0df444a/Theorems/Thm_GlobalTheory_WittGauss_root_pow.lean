-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_root_pow
-- name    : GlobalTheory.WittGauss.root_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:12:03.33056+00:00
-- url     : https://prove2.me/theorems/b0cdf341-3cd0-49d7-b911-a690eab67c01
-- title:
--   Witt Gauss: root pow
-- statement:
--   The Witt Gauss construction uses the root pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L151-L154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector

theorem GlobalTheory.WittGauss.root_pow (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ ((1 : ℝ) / (p : ℝ) ^ n)) ^ p ^ n = t := by sorry
