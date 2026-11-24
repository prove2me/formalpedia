-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_teichmuller_mul_int
-- name    : GlobalTheory.WittGauss.teichmuller_mul_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:12.514717+00:00
-- url     : https://prove2.me/theorems/7c855e75-f165-437e-a59d-5cc4d3e58032
-- title:
--   Witt Gauss: teichmuller mul int
-- statement:
--   The Witt Gauss construction uses the teichmuller mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L34-L38

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

theorem GlobalTheory.WittGauss.teichmuller_mul_int (p : ℕ) [Fact p.Prime] {S : Type} (t : MvPolynomial S ℤ)
    (x : WittVector p (MvPolynomial S ℤ)) : teichmuller p t * x = scaleCoeff p t x := by sorry
