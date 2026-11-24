-- Prove2me | Theorems.Thm_GlobalTheory_T_local_splitting_kernel_base_change
-- name    : GlobalTheory.T.local_splitting_kernel_base_change
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:40.199182+00:00
-- url     : https://prove2.me/theorems/21ec3ef7-f0a9-45eb-a964-06ef65b23d6a
-- title:
--   T: local splitting kernel base change
-- statement:
--   The T construction uses the local splitting kernel base change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalSplittingKernelBaseChangeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalSplittingKernelBaseChangeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChange
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChangeStatement
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

theorem GlobalTheory.T.local_splitting_kernel_base_change : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by sorry
