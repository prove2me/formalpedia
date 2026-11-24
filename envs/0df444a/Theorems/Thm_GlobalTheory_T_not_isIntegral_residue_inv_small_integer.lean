-- Prove2me | Theorems.Thm_GlobalTheory_T_not_isIntegral_residue_inv_small_integer
-- name    : GlobalTheory.T.not_isIntegral_residue_inv_small_integer
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:32.290221+00:00
-- url     : https://prove2.me/theorems/dc8d7da0-884c-4563-a37e-adc80e003e7e
-- title:
--   T: not is Integral residue inv small integer
-- statement:
--   The T construction uses the not is Integral residue inv small integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsIntegralResidueInvSmallIntegerStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotIsIntegralResidueInvSmallIntegerStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsIntegralResidueInvSmallInteger
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsIntegralResidueInvSmallIntegerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.not_isIntegral_residue_inv_small_integer : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by sorry
