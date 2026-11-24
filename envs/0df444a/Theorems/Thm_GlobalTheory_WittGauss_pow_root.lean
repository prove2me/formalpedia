-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_pow_root
-- name    : GlobalTheory.WittGauss.pow_root
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:17.126512+00:00
-- url     : https://prove2.me/theorems/52d6339a-ddf8-43f3-b5cf-d8a26b3e6411
-- title:
--   Witt Gauss: pow root
-- statement:
--   The Witt Gauss construction uses the pow root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L156-L159

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

theorem GlobalTheory.WittGauss.pow_root (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (t ^ p ^ n) ^ ((1 : ℝ) / (p : ℝ) ^ n) = t := by sorry
