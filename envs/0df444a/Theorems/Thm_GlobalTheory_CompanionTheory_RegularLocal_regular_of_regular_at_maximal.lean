-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RegularLocal_regular_of_regular_at_maximal
-- name    : GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:44.027202+00:00
-- url     : https://prove2.me/theorems/e5dc56e6-b56b-43c8-8a97-53a0c6b8f39c
-- title:
--   Regular Local: regular of regular at maximal
-- statement:
--   The Regular Local construction uses the regular of regular at maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalSplittingKernelBaseChange.lean#L6-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalSplittingKernelBaseChange.lean#L6-L92

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RegularLocal

theorem GlobalTheory.CompanionTheory.RegularLocal.regular_of_regular_at_maximal : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by sorry
