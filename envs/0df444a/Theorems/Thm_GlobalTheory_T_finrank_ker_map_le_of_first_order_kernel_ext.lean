-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_ker_map_le_of_first_order_kernel_ext
-- name    : GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:39:17.135856+00:00
-- url     : https://prove2.me/theorems/597841ed-8fa8-4455-a652-a0393562447b
-- title:
--   T: finrank ker map le of first order kernel ext
-- statement:
--   The T construction uses the finrank ker map le of first order kernel ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExtStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExtStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finrank_ker_map_le_of_first_order_kernel_ext : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (a e : ℕ) (Φ : Matrix (Fin a) (Fin a) k) (U : Type) [AddCommGroup U] [Module k U] [Module.Finite k U] (t u : LinearMap.ker Φ.mulVecLin →ₗ[k] U), (∀ x0 x1 : Fin (e + 1) → LinearMap.ker Φ.mulVecLin, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → Module.finrank K (LinearMap.ker (Φ.map (algebraMap k K)).mulVecLin) ≤ Module.finrank k U + e := by sorry
