-- Prove2me | Theorems.Thm_GlobalTheory_NotIntegral_inv_small_not_integral
-- name    : GlobalTheory.NotIntegral.inv_small_not_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:02.791225+00:00
-- url     : https://prove2.me/theorems/6514032b-ae22-4da8-848b-182486cfa794
-- title:
--   Not Integral: inv small not integral
-- statement:
--   The Not Integral construction uses the inv small not integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsIntegralResidueInvSmallInteger.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsIntegralResidueInvSmallInteger.lean#L8-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsIntegralResidueInvSmallInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.NotIntegral

theorem GlobalTheory.NotIntegral.inv_small_not_integral : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by sorry
