-- Prove2me | Theorems.Thm_GlobalTheory_T_eigenvector_lift_of_surjection
-- name    : GlobalTheory.T.eigenvector_lift_of_surjection
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:17.251413+00:00
-- url     : https://prove2.me/theorems/a8dc5e78-1e02-4068-ac12-5323b1ce823f
-- title:
--   T: eigenvector lift of surjection
-- statement:
--   The T construction uses the eigenvector lift of surjection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EigenvectorLiftOfSurjectionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EigenvectorLiftOfSurjectionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjection
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eigenvector_lift_of_surjection : ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'), Function.Surjective f → f ∘ₗ T = S ∘ₗ f → ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by sorry
