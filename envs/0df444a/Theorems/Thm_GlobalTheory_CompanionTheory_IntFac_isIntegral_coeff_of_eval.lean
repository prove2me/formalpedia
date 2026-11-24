-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_coeff_of_eval
-- name    : GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:25.091027+00:00
-- url     : https://prove2.me/theorems/3ed5809a-5019-41a9-878b-18cedb74c257
-- title:
--   Int Fac: is Integral coeff of eval
-- statement:
--   The Int Fac construction uses the is Integral coeff of eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L7-L39

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

theorem GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ u : ℂ, IsIntegral ℂ (F.eval (algebraMap ℂ A u))) (k : ℕ) :
    IsIntegral ℂ (F.coeff k) := by sorry
