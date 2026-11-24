-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_teichmuller_mul_eq
-- name    : GlobalTheory.WittGauss.teichmuller_mul_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:12.278709+00:00
-- url     : https://prove2.me/theorems/81ba9881-c686-4fa2-9079-a1a89607522a
-- title:
--   Witt Gauss: teichmuller mul eq
-- statement:
--   The Witt Gauss construction uses the teichmuller mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L40-L46

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

theorem GlobalTheory.WittGauss.teichmuller_mul_eq (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (t : S)
    (x : WittVector p S) : teichmuller p t * x = scaleCoeff p t x := by sorry
