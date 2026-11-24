-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IntFac_isIntegral_coeff_of_monic_dvd
-- name    : GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:48:24.749939+00:00
-- url     : https://prove2.me/theorems/4f1089f9-0349-4ec7-963f-6a98baefc32d
-- title:
--   Int Fac: is Integral coeff of monic dvd
-- statement:
--   The Int Fac construction uses the is Integral coeff of monic dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MonicFactorCoefficientsIntegral.lean#L46-L55

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

theorem GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd (A : Type) [CommRing A] [Algebra ℂ A] (F G : A[X])
    (hF : F.Monic) (hG : G.Monic) (hd : G ∣ F) (h : ∀ k, IsIntegral ℂ (F.coeff k)) (k : ℕ) :
    IsIntegral ℂ (G.coeff k) := by sorry
