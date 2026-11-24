-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_residue_comap_involution_iff
-- name    : GlobalTheory.T.isIntegral_residue_comap_involution_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:49.014493+00:00
-- url     : https://prove2.me/theorems/5bdde103-f5db-4ad3-b9de-8cdff564b536
-- title:
--   T: is Integral residue comap involution iff
-- statement:
--   The T construction uses the is Integral residue comap involution iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralResidueComapInvolutionIffStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralResidueComapInvolutionIffStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIffStatement
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

theorem GlobalTheory.T.isIntegral_residue_comap_involution_iff : ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A), IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔ IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by sorry
