-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isIntegral_mk_comap_sigma_iff
-- name    : GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:31.364847+00:00
-- url     : https://prove2.me/theorems/c4749e0c-aa74-4077-a64b-f51363aa7486
-- title:
--   Inv Alg: is Integral mk comap sigma iff
-- statement:
--   The Inv Alg construction uses the is Integral mk comap sigma iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralResidueComapInvolutionIff.lean#L49-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralResidueComapInvolutionIff.lean#L49-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralResidueComapInvolutionIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory.UnitLemma.SwapInt

theorem GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by sorry
