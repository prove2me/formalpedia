-- Prove2me | Theorems.Thm_GlobalTheory_T_kernel_free_at_primes_of_constant_rank
-- name    : GlobalTheory.T.kernel_free_at_primes_of_constant_rank
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:09.9809+00:00
-- url     : https://prove2.me/theorems/371b958d-704d-4a20-941a-6afd35d5b13c
-- title:
--   T: kernel free at primes of constant rank
-- statement:
--   The T construction uses the kernel free at primes of constant rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelFreeAtPrimesOfConstantRankStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelFreeAtPrimesOfConstantRankStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRank
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRankStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.kernel_free_at_primes_of_constant_rank : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) → Module.Projective R (LinearMap.ker d) → (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) → ∀ (p : Ideal R) [p.IsPrime], Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.Finite (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.finrank (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by sorry
