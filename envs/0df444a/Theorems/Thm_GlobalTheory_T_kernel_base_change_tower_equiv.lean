-- Prove2me | Theorems.Thm_GlobalTheory_T_kernel_base_change_tower_equiv
-- name    : GlobalTheory.T.kernel_base_change_tower_equiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:47.358616+00:00
-- url     : https://prove2.me/theorems/d9adba86-b199-4f15-b4bc-b1bcf14a3e36
-- title:
--   T: kernel base change tower equiv
-- statement:
--   The T construction uses the kernel base change tower equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelBaseChangeTowerEquivStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/KernelBaseChangeTowerEquivStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquiv
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquivStatement
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

theorem GlobalTheory.T.kernel_base_change_tower_equiv : ∀ (R A K Q P : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P), Nonempty (LinearMap.ker ((d.baseChange A).baseChange K) ≃ₗ[K] LinearMap.ker (d.baseChange K)) := by sorry
