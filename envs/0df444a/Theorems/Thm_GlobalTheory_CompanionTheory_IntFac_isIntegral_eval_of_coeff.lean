-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_eval_of_coeff
-- name    : GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:48:11.317535+00:00
-- url     : https://prove2.me/theorems/33dc605f-c153-405e-a1a2-e5c2fa838fbe
-- title:
--   Int Fac: is Integral eval of coeff
-- statement:
--   The Int Fac construction uses the is Integral eval of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L41-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IntFac

theorem GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ k, IsIntegral ℂ (F.coeff k)) (u : ℂ) : IsIntegral ℂ (F.eval (algebraMap ℂ A u)) := by sorry
