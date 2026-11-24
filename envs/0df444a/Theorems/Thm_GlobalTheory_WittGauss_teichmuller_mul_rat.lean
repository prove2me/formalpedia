-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_teichmuller_mul_rat
-- name    : GlobalTheory.WittGauss.teichmuller_mul_rat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:13.004026+00:00
-- url     : https://prove2.me/theorems/2573e232-cf7f-435e-8324-05601d11bc0b
-- title:
--   Witt Gauss: teichmuller mul rat
-- statement:
--   The Witt Gauss construction uses the teichmuller mul rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L28-L32

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

theorem GlobalTheory.WittGauss.teichmuller_mul_rat (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℚ)
    (x : WittVector p (MvPolynomial S ℚ)) : teichmuller p t * x = scaleCoeff p t x := by sorry
