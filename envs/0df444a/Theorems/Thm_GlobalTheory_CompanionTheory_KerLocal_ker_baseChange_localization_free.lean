-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KerLocal_ker_baseChange_localization_free
-- name    : GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:41.188204+00:00
-- url     : https://prove2.me/theorems/f98bd7b4-5019-4244-9a9b-aad6c2694b18
-- title:
--   Ker Local: ker base Change localization free
-- statement:
--   The Ker Local construction uses the ker base Change localization free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelFreeAtPrimesOfConstantRank.lean#L6-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelFreeAtPrimesOfConstantRank.lean#L6-L31

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerLocal

theorem GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free :
    ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
      (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) →
      Module.Projective R (LinearMap.ker d) →
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) →
      ∀ (p : Ideal R) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.Finite (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.finrank (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by sorry
