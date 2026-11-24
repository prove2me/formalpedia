-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_coeff_of_shifted_product
-- name    : GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:58.579533+00:00
-- url     : https://prove2.me/theorems/e3fdffc6-a5cd-43aa-bc3c-e70e28949c41
-- title:
--   Int Fac: is Integral coeff of shifted product
-- statement:
--   The Int Fac construction uses the is Integral coeff of shifted product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L59-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L59-L81

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

theorem GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic →
      (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) *
        Q.eval (algebraMap ℂ A (u + c₂)))) →
      ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by sorry
