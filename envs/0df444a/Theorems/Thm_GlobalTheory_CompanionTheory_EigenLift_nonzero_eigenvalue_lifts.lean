-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EigenLift_nonzero_eigenvalue_lifts
-- name    : GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:11.253981+00:00
-- url     : https://prove2.me/theorems/11718da4-8517-4e6b-a072-5c10b84020a4
-- title:
--   Eigen Lift: nonzero eigenvalue lifts
-- statement:
--   The Eigen Lift construction uses the nonzero eigenvalue lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EigenvectorLiftOfSurjection.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EigenvectorLiftOfSurjection.lean#L38-L44

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EigenLift

theorem GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by sorry
